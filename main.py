from z3 import *
import calendar
from datetime import date, timedelta
import numpy as np


def z_sum(z_list):
    """Sums a list of BitVecRef types and returns a BitVecRef. This is a z3 compatible sum."""
    s = 0
    for item in z_list:
        s += item
    return s


def daily_rest(roles, i, j):
    """
    Returns the required days rest between shifts (roles[i] and roles[j]), so there is at least 11 hours rest between
    them.
    """
    if roles[i].end > 24:
        return range(0, 0) if roles[j].start - roles[i].end + 24 >= 11 else range(1, 2)
    else:
        return range(0, 0) if 24 - roles[i].end + roles[i].start >= 11 else range(1, 2)


def night_rest(roles, i, j):
    """
    Returns the required days rest between a night shift (roles[i]) and another shift (roles[j]), so there is at least
    46 hours rest between them. The rest is only required coming off a night shift (i.e. the next shift is not a night
    shift) or if four consecutive night shifts have been worked.
    """
    return range(1, 3) if roles[j].start - roles[i].end + 24 >= 22 else range(1, 4)


def long_rest(roles, i, j):
    """
    Returns the required days rest between a long shift (roles[i]) and another shift (roles[j]), so there is at least 48
    hours rest between them. The rest is only required if four consecutive long shifts have been worked.
    """
    if roles[i].end > 24:
        return range(1, 3) if roles[j].start - roles[i].end + 24 >= 24 else range(1, 4)
    else:
        return range(1, 2) if 24 - roles[i].end + roles[i].start >= 24 else range(1, 3)


class Rota:
    def __init__(self, start, end, people, mandatory_roles, optional_roles):
        """
        :type start: date
        :type end: date
        :type people: list[Employee]
        :type mandatory_roles: list[Shift]
        :type optional_roles: list[Shift]
        """
        self.model = None
        self.start = start
        self.end = end
        self.length = (end - start).days

        self.people_objs = people
        self.role_objs = mandatory_roles + optional_roles

        self.mandatory_roles = range(len(mandatory_roles))
        self.optional_roles = range(len(mandatory_roles) + 1, len(optional_roles))
        self.roles = range(len(optional_roles) + len(mandatory_roles))
        self.people = range(len(people))
        self.nights = [role for role in self.roles if self.role_objs[role].night]
        self.longs = [role for role in self.roles if self.role_objs[role].long]

        self.night_rest = {n: [night_rest(self.role_objs, n, r) for r in self.roles] for n in self.nights}
        self.long_rest = {l: [long_rest(self.role_objs, l, r) for r in self.roles] for l in self.longs}
        self.daily_rest = {r1: [daily_rest(self.role_objs, r1, r2) for r2 in self.roles] for r1 in self.roles}
        self.test = {r1: [f"{r1}{r2}" for r2 in self.roles] for r1 in self.roles}

        self.shifts = {start + timedelta(days=d): self.create_shift(d) for d in range(self.length)}
        self.o = Optimize()

        for shift in self.shifts.values():
            # each mandatory role must be taken
            [self.o.add(PbEq([(x, 1) for x in shift[mr, :]], 1)) for mr in self.mandatory_roles]

            # each person may take at most one role
            [self.o.add(AtMost(*[x for x in shift[:, p]], 1)) for p in self.people]

        # restricted times for each staff member removed
        for p, person_obj in zip(self.people, self.people_objs):
            if person_obj.holiday is not None:
                for holiday in person_obj.holiday:
                    if start <= holiday < end:
                        self.o.add(PbEq([(x, 1) for x in self.shifts[holiday][:, p]], 0))

            if person_obj.start is not None and start < person_obj.start <= end:
                for i in range((person_obj.start - self.start).days):
                    self.o.add(PbEq([(x, 1) for x in self.get_shift(i)[:, p]], 0))

            if person_obj.end is not None and start < person_obj.end <= end:
                for i in range((person_obj.end - self.start).days, self.length):
                    self.o.add(PbEq([(x, 1) for x in self.get_shift(i)[:, p]], 0))

        # max four long shifts then 48 hrs rest after final shift
        for lr in self.longs:
            for i in range(4, self.length):
                self.o.add(
                    Not(
                        And(
                            And(
                                [Or(
                                    [self.get_shift(day=i, sub=j)[r, p] for r in self.longs]) for j in range(1, 4)]
                            ),
                            self.get_shift(day=i)[lr, p],
                            Not(
                                Or(
                                    [self.get_shift(day=i, add=j)[r, p] for r in self.roles for j in
                                     self.long_rest[lr][r] if i + j < self.length]
                                )
                            )

                        )
                    )
                )

        # max four night shifts
        for i in range(5, self.length):
            self.o.add(
                Not(
                    And([Or([self.get_shift(day=i, sub=j)[r, p] for r in self.nights]) for j in range(5)])
                )
            )

        # if a shift is a night shift, either it must be followed by another night shift, or 46 hrs rest
        for nr in self.nights:
            for i in range(1, self.length):
                self.o.add(
                    Not(
                        And(
                            self.get_shift(day=i, sub=1)[nr, p],
                            Not(
                                Xor(
                                    Or([self.get_shift(day=i)[r, p] for r in self.nights]),
                                    Or([self.get_shift(day=i, add=j)[r, p] for r in self.roles for j in
                                        self.night_rest[nr][r] if i + j < self.length])
                                )
                            )
                        )
                    )
                )

        # rest of 11 hours between shifts
        for i in range(self.length):
            for r1 in self.roles:
                for r2 in self.roles:
                    if self.daily_rest[r1][r2] != range(0, 0):
                        self.o.add(
                            Not(
                                And(
                                    self.get_shift(day=i)[r1, p],
                                    Or(
                                        [self.get_shift(day=i, add=j)[r2, p] for j in self.daily_rest[r1][r2] if
                                         i + j < self.length]
                                    )
                                )
                            )
                        )

        # max seven consecutive shifts
        for i in range(8, self.length):
            self.o.add_soft(
                Not(
                    And(
                        [Or(
                            [self.get_shift(day=i, sub=j)[r, p] for r in self.roles]) for j in range(8)]
                    )
                )
            )

        # max 1 in 3 weekends worked
        weekends = []
        for i, date in enumerate(self.shifts.keys()):
            if calendar.weekday(date.year, date.month, date.day) == 5:
                weekends.append(
                    Or(
                        Or(
                            [self.get_shift(day=i, sub=j)[r, p] for r in self.nights for j in range(1, 2) if
                             i - j >= 0],
                        ),
                        Or(
                            [self.get_shift(day=i, add=j)[r, p] for r in self.roles for j in range(0, 2) if
                             i + j < self.length]
                        )
                    )
                )
        for i in range(len(weekends) - 2):
            self.o.add(
                Not(
                    And(
                        weekends[i],
                        weekends[i + 1],
                        weekends[i + 2]
                    )
                )
            )

    def get_shift(self, day, sub=0, add=0):
        """Returns the (day - sub + add) shift."""
        return self.shifts[self.start + timedelta(days=day - sub + add)]

    def create_shift(self, shift_number):
        """
        :type shift_number: int

        Each shift is represented by a 2d ndarray of z3.Bools. Each row is a role, each column is a person. The
        reference to each z3.Bool is given by {shift_number}{colum/person}{row/role}. For example, the first shift, for
        four people and three roles is:

                    p0   p1   p2   p3
               r0 [[000, 010, 020, 030],
               r2  [001, 011, 012, 013],
               r3  [002, 012, 022, 023]]
        """
        return np.array([[Bool(f"{shift_number}{person}{role}") for person in self.people] for role in self.roles])

    def evaluate(self):
        if self.o.check() == sat:
            self.model = self.o.model()

    def print_rota(self):
        if self.model:
            print(f"{'':<20}", end="")
            for person in self.people:
                print(f"｜{f'person {person}':^21}", end="")
            print("｜")
            shift_info = [f"｜{self.role_objs[i].start:<7}{self.role_objs[i].end:<7}{self.role_objs[i].length:<7}" for i in self.roles] + ["｜" + " " * 21]
            for day, shifts in self.shifts.items():
                print(f"{calendar.day_name[day.weekday()]: <10}{day.strftime('%d/%m/%Y'): >10}", end="")
                roles_worked = {i: -1 for i in self.people}
                for person in self.people:
                    for role in self.roles:
                        if bool(self.model[shifts[role, person]]):
                            roles_worked[person] = role
                            continue
                [print(shift_info[roles_worked[i]], end="") for i in self.people]
                print("｜")


class Employee:
    def __init__(self, start=None, end=None, holiday=None, can_do_longs=True, can_do_nights=True):
        """
        :type start: date
        :type end: date
        :type holiday: set[date]
        :type can_do_longs: bool
        :type can_do_nights: bool
        """
        self.start = start
        self.end = end
        self.holiday = holiday
        self.can_work_longs = can_do_longs
        self.can_work_nights = can_do_nights


class Shift:
    def __init__(self, start, length):
        """
        :type start: float
        :type length: float
        """
        self.start = start
        self.end = start + length
        self.length = length
        self.long = length > 10
        self.night = (start + length >= 26) or (start <= 3 and length >= 3)


def main():
    staff = [
        Employee(holiday={date(2023, 1, 1)}),
        Employee(holiday={date(2023, 6, 1)}),
        Employee(),
        Employee(start=date(2023, 1, 28), end=date(2023, 3, 1), holiday={date(2023, 2, 2)}),
        Employee(),
        Employee(),
    ]

    # a long night shift and a long day shift
    mandatory_roles = [
        Shift(20.5, 13),
        Shift(8.5, 13)
    ]

    optional_roles = [
        Shift(9, 8)
    ]

    r = Rota(date(2023, 1, 1), date(2023, 7, 1), staff, mandatory_roles, optional_roles)
    r.evaluate()
    r.print_rota()


if __name__ == '__main__':
    main()
