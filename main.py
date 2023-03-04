from z3 import *
import calendar
from datetime import date, timedelta
import numpy as np


def night_rest(roles, i, j):
    """Returns the required days rest between shifts, if shift1 has been worked and is a night shift"""
    return 3 if (roles[i].start + roles[j].length) - 22 <= roles[j].start else 4


def long_rest(shift1, shift2):
    """Returns the required days rest between shifts, if shift1 is the fourth consecutive long shift worked"""
    end = shift1.start + shift1.length
    if end < 24:
        return 2
    elif end > 24 and end - 24 <= shift2.start:
        return 3
    else:
        return 4


class Rota:
    def __init__(self, start, end, staff, mandatory_roles, optional_roles):
        """
        :type start: date
        :type end: date
        :type staff: list[Employee]
        :type mandatory_roles: list[Shift]
        :type optional_roles: list[Shift]
        """
        self.start = start
        self.end = end
        self.length = (end - start).days

        self.staff = staff
        self.roles = mandatory_roles + optional_roles

        self.no_mandatory_roles = len(mandatory_roles)
        self.no_optional_roles = len(optional_roles)
        self.no_roles = self.no_mandatory_roles + self.no_optional_roles
        self.no_staff = len(staff)

        self.night_indexes = [i for i in range(len(self.roles)) if self.roles[i].night]
        self.long_indexes = [i for i in range(len(self.roles)) if self.roles[i].long]
        self.night_rest = {i: [night_rest(self.roles, i, j) for j in range(self.no_roles)] for i in self.night_indexes}
        self.long_rest = {i: [night_rest(self.roles, i, j) for j in range(self.no_roles)] for i in self.long_indexes}
        self.shifts = {start + timedelta(days=i): self.create_shift(i) for i in range(self.length)}
        self.o = Optimize()

        for role in self.shifts.values():
            # each mandatory role must be taken
            [self.o.add(PbEq([(x, 1) for x in role[r, :]], 1)) for r in range(self.no_mandatory_roles)]

            # each person may take at most one role
            [self.o.add(AtMost(*[x for x in role[:, p]], 1)) for p in range(self.no_staff)]

        # restricted times for each staff member removed
        for p in range(self.no_staff):
            if staff[p].holiday is not None:
                [self.o.add(PbEq([(x, 1) for x in self.shifts[date][:, p]], 0)) for date in staff[p].holiday if
                 start <= date < end]

            if staff[p].start is not None and start < staff[p].start <= end:
                for i in range((self.start - staff[p].start).days):
                    self.o.add(PbEq([(x, 1) for x in self.get_shift(i)[:, p]], 0))

            if staff[p].end is not None and end > staff[p].end >= start:
                for i in range((self.end - staff[p].end).days):
                    self.o.add(PbEq([(x, 1) for x in self.get_shift(i)[:, p]], 0))

        # max four long shifts then 48 hrs rest after final shift
        for p in range(self.no_staff):
            for l in self.long_indexes:
                for i in range(5, self.length):
                    self.o.add(
                        Not(And(Or([self.get_shift(i=i, j=4)[r, p] for r in self.long_indexes]),
                                Or([self.get_shift(i=i, j=3)[r, p] for r in self.long_indexes]),
                                Or([self.get_shift(i=i, j=2)[r, p] for r in self.long_indexes]),
                                self.get_shift(i=i, j=1)[l, p],
                                Or([self.get_shift(i=i, k=k)[r, p] for k in self.long_rest[l]
                                    for r in range(self.no_roles) if i + k < self.length]))))

        # max four night shifts
        for p in range(self.no_staff):
            for i in range(5, self.length):
                self.o.add(Not(And(Or([self.get_shift(i=i, j=4)[r, p] for r in self.night_indexes]),
                                   Or([self.get_shift(i=i, j=3)[r, p] for r in self.night_indexes]),
                                   Or([self.get_shift(i=i, j=2)[r, p] for r in self.night_indexes]),
                                   Or([self.get_shift(i=i, j=1)[r, p] for r in self.night_indexes]),
                                   Or([self.get_shift(i=i, j=0)[r, p] for r in self.night_indexes]))))

        # if a shift is a night shift, either it must be followed by another night shift, or 46 hrs rest
        for p in range(self.no_staff):
            for n in self.night_indexes:
                for i in range(1, self.length):
                    Not(And(self.get_shift(i=i, j=1)[n, p],
                            Not(Xor(Or([self.get_shift(i=i, k=k)[r, p] for k in self.night_rest[n]
                                        for r in range(self.no_roles) if i + k < self.length]),
                                    Or([self.get_shift(i=i)[r, p] for r in self.night_indexes])))))

    def get_shift(self, i, j=0, k=0):
        """Returns the (ith - jth + kth) shift."""
        return self.shifts[self.start + timedelta(days=i - j + k)]

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
        return np.array([[Bool(f"{shift_number}{i}{j}") for i in range(self.no_staff)] for j in range(self.no_roles)])

    def evaluate(self):
        if self.o.check() == sat:
            return self.o.model()
        else:
            return False


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
        self.length = length
        self.long = length > 10
        self.night = (start + length >= 26) or (start <= 3 and length >= 3)


def main():
    staff = [Employee(holiday={date(2023, 1, 1)}), Employee(holiday={date(2023, 6, 1)}), Employee(),
             Employee(start=date(2023, 1, 28), end=date(2023, 3, 1), holiday={date(2023, 2, 2)})]

    # a long night shift and a long day shift
    mandatory_roles = [Shift(20.5, 13), Shift(8.5, 13)]

    optional_roles = [Shift(9, 8)]
    roles = mandatory_roles + optional_roles

    r = Rota(date(2023, 1, 1), date(2023, 7, 1), staff, mandatory_roles, optional_roles)
    m = r.evaluate()
    print(m if m is False else "True")


if __name__ == '__main__':
    main()
