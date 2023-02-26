from z3 import *
import calendar
from datetime import date, timedelta
import numpy as np


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
        self.no_mandatory_roles = len(mandatory_roles)
        self.no_optional_roles = len(optional_roles)
        self.no_roles = self.no_mandatory_roles + self.no_optional_roles
        self.no_staff = len(staff)
        self.mandatory_roles = mandatory_roles
        self.optional_roles = optional_roles
        self.shifts = {start + timedelta(days=i): self.create_shift(i) for i in range(self.length)}
        self.o = Optimize()

        for shift in self.shifts.values():
            # each mandatory role must be taken
            [self.o.add(PbEq([(x, 1) for x in shift[i, :]], 1)) for i in range(self.no_mandatory_roles)]

            # each person may take at most one role
            [self.o.add(AtMost(*[x for x in shift[:, i]], 1)) for i in range(self.no_staff)]

        # restricted times for each staff member removed
        for i in range(self.no_staff):
            if staff[i].holiday is not None:
                [self.o.add(PbEq([(x, 1) for x in self.shifts[date][:, i]], 0)) if start <= date < end
                 else None for date in staff[i].holiday]

            if staff[i].start is not None and start < staff[i].start <= end:
                for j in range((self.start - staff[i].start).days):
                    self.o.add(PbEq([(x, 1) for x in self.shifts[start + timedelta(days=j)][:, i]], 0))

            if staff[i].end is not None and end > staff[i].end >= start:
                for j in range((self.end - staff[i].end).days):
                    self.o.add(PbEq([(x, 1) for x in self.shifts[start + timedelta(days=j)][:, i]], 0))

        for i, shift in zip(range(self.no_mandatory_roles), mandatory_roles):
            if shift.long or shift.night:
                [self.o.add(Not(And(prev_shifts(night, 4), night))) for j in range(5, self.length)]

    def create_shift(self, shift_number):
        """
        :type shift_number: int

        Each shift is represented by a 2d ndarray of z3.Bools. Each row is a role, each column is a person. The
        reference to each z3.Bool is given by {shift_number}{colum}{row}. For example, the first shift, for four
        employees and three shifts is:

                    p0   p1   p2   p3
               s0 [[000, 010, 020, 030],
               s2  [001, 011, 012, 013],
               s3  [002, 012, 022, 023]]
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
    mandatory_roles = [Shift(20.5, 9.5), Shift(8.5, 2)]

    optional_roles = [Shift(9, 5)]

    r = Rota(date(2023, 1, 1), date(2023, 7, 1), staff, mandatory_roles, optional_roles)
    m = r.evaluate()
    print(m)

if __name__ == '__main__':
    main()
