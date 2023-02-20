from z3 import *
import calendar
from datetime import date, timedelta


def z_sum(z_list):
    """
    :param z_list: a list of ArithRef objects
    :type z_list: list[ArithRef]
    :return: the sum of the items in the list
    :rtype: ArithRef
    """
    s = 0
    for item in z_list:
        s += item
    return s


def is_weekend(date):
    """
    :param date: the date to query
    :type date: date
    :return: true if the date is a weekend else false
    :rtype: bool
    """
    return calendar.weekday(date.year, date.month, date.day) >= 5


class Rota:
    def __init__(self, start_date, end_date):
        """
        :param start_date: the start date of the rota
        :type start_date: date
        :param end_date: the end date of the rota
        :type end_date: date
        """
        self.start_date = start_date
        self.end_date = end_date
        self.length = (end_date - start_date).days
        self.last_shift = end_date - timedelta(days=1)
        self.start_times = {start_date + timedelta(days=i): z3.BitVec(f's{i}', 24) for i in range(self.length)}
        self.end_times = {start_date + timedelta(days=i): z3.BitVec(f'e{i}', 24) for i in range(self.length)}

    def start_time(self, date):
        """
        :param date: the date of the shift
        :type date: date
        :return: the start time of the shift
        :rtype: z3.ArithRef
        """
        return self.start_times[date]

    def end_time(self, date):
        """
        :param date: the date of the shift
        :type date: date
        :return: the end time of the shift
        :rtype: z3.ArithRef
        """
        return self.end_times[date]

    def shift_length(self, date):
        """
        :param date: the date of the shift
        :type date: date
        :return: the shift length in seconds
        :rtype: z3.ArithRef
        """
        return If(
            self.start_time(date) == BitVecVal(16777215, 24),
            BitVecVal(0, 24),
            If(
                self.end_time(date) == BitVecVal(16777215, 24),
                self.end_time(date + timedelta(days=1)) - self.start_time(date),
                self.end_time(date) - self.start_time(date)
            )
        )

    def is_long_day(self, date):
        """
        :param date: the date of the shift
        :type date: date
        :return: true if the shift is longer than 10 hours else false
        :rtype: z3.ArithRef

        Notes:
            • 10hrs = 3600s
        """
        return self.shift_length(date) > BitVecVal(3600, 24)

    def is_long_evening_shift(self, date):
        """
        :param date: the date of the shift
        :type date: date
        :return: true if the shift starts before 16:00 and ends after 23:00
        :rtype: z3.ArithRef

        Notes:
            • 16:00 = 57600s
            • 23:00 = 82800s
        """
        return And(
            self.start_time(date) < BitVecVal(57600, 24),
            self.end_time(date) > BitVecVal(82800, 24)
        )

    def average_working_week(self):
        """
        :return: the average working week in seconds
        :rtype: z3.ArithRef

        Notes:
            • 1 day = 86400s
            • 7 days = 604800s
        """
        return UDiv(
            z_sum([self.shift_length(self.start_date + timedelta(days=i)) for i in range(self.length - 1)]),
            BitVecVal((self.length * 86400) // 604800, 24)
        )

    def end_time_constraints(self, date):
        return Or(
            And(
                Or(
                    self.end_time(date) > self.start_time(date),
                    self.start_time(date) == BitVecVal(16777215, 24)
                ),
                self.end_time(date) >= BitVecVal(0, 24),
                self.end_time(date) < BitVecVal(86400, 24),
                self.end_time(date) % BitVecVal(1800, 24) == BitVecVal(0, 24),
            ),
            self.end_time(date) == BitVecVal(16777215, 24)
        )

    def start_time_constraints(self, date):
        return Or(
            And(
                self.start_time(date) >= BitVecVal(0, 24),
                self.start_time(date) < BitVecVal(86400, 24),
                self.start_time(date) % BitVecVal(1800, 24) == BitVecVal(0, 24),
            ),
            self.start_time(date) == BitVecVal(16777215, 24)
        )

    def last_shift_constraints(self):
        return Or(
            And(
                self.start_time(self.last_shift) >= BitVecVal(0, 24),
                self.start_time(self.last_shift) < BitVecVal(86400, 24),
                self.start_time(self.last_shift) % BitVecVal(1800, 24) == BitVecVal(0, 24),
                Or(
                    self.end_time(self.last_shift) > self.start_time(self.last_shift),
                    self.start_time(self.last_shift) == BitVecVal(16777215, 24)
                ),
                self.end_time(self.last_shift) >= BitVecVal(0, 24),
                self.end_time(self.last_shift) < BitVecVal(86400, 24),
                self.end_time(self.last_shift) % BitVecVal(1800, 24) == BitVecVal(0, 24),
            ),
            And(
                self.start_time(self.last_shift) == BitVecVal(16777215, 24),
                self.end_time(self.last_shift) == BitVecVal(16777215, 24)
            )
        )


class RotaCreator:
    def __init__(self, start_date, end_date):
        """
        :param start_date: the start date of the rota
        :type start_date: date
        :param end_date: the end date of the rota
        :type end_date: date
        """
        self.rota = Rota(start_date, end_date)
        self.o = Optimize()

    def set_constraints(self):
        """
        Adds the following constraints to the optimizer:
        https://www.nhsemployers.org/system/files/media/Rota-rules-at-a-glance_0.pdf

        It also adds some additional constraints to stop the application blowing up and to behave logically:
            •
        """
        # the last shift constraints
        self.o.add(self.rota.last_shift_constraints())

        # add general shift time constraints
        for i in range(self.rota.length - 1):
            self.o.add(self.rota.end_time_constraints(self.rota.start_date + timedelta(days=i)))
            self.o.add(self.rota.start_time_constraints(self.rota.start_date + timedelta(days=i)))

        # max 48-hour average working week
        self.o.add(self.rota.average_working_week() <= BitVecVal(172800, 24))

        # max 13-hour shift length
        for i in range(self.rota.length - 1):
            self.o.add(self.rota.shift_length(self.rota.start_date + timedelta(days=i)) <= BitVecVal(46800, 24))

        self.o.add(self.rota.average_working_week() > BitVecVal(72000, 24))

    def evaluate(self):
        if self.o.check() == sat:
            m = self.o.model()
            return m
        else:
            return False


def main():
    start_date = date(2023, 1, 1)
    end_date = date(2023, 3, 1)
    r = RotaCreator(start_date, end_date)
    r.set_constraints()
    m = r.evaluate()
    print(m)


if __name__ == '__main__':
    main()
