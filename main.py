import z3
from z3 import *
import calendar
from datetime import date, timedelta

NONE = BitVecVal(16777215, 24)
DAYS_1 = timedelta(days=1)
DAYS_2 = timedelta(days=2)
DAYS_3 = timedelta(days=3)
ZERO = BitVecVal(0, 24)
HOURS_2 = BitVecVal(7200, 24)
HOURS_6 = BitVecVal(21600, 24)
HOURS_10 = BitVecVal(3600, 24)
HOURS_16 = BitVecVal(57600, 24)
HOURS_23 = BitVecVal(82800, 24)
HOURS_24 = z3.BitVecVal(86400, 24)
MINUTES_30 = BitVecVal(1800, 24)


def z_sum(z_list):
    """Sums a list of BitVecRef types"""
    s = 0
    for item in z_list:
        s += item
    return s


def is_sat(date):
    """Returns True of the date is a Saturday else False"""
    return calendar.weekday(date.year, date.month, date.day) == 5


def four_prev_shifts(date, shift_type_function):
    """Returns True if the output of the provided function is True for the previous four days"""
    c = [shift_type_function(date - timedelta(days=i)) for i in range(1, 5)]
    return And(c[0], c[1], c[2], c[3])


class Rota:
    def __init__(self, start_date, end_date):
        """
        :param start_date: the start date of the rota
        :type start_date: date
        :param end_date: the end date of the rota
        :type end_date: date
        """
        self.first_shift = start_date
        self.last_shift = end_date - DAYS_1
        self.length = (end_date - start_date).days
        self.start_times = {start_date + timedelta(days=i): z3.BitVec(f's{i}', 24) for i in range(self.length)}
        self.end_times = {start_date + timedelta(days=i): z3.BitVec(f'e{i}', 24) for i in range(self.length)}
        for i in range(self.length, self.length + 3):
            self.start_times[self.first_shift + timedelta(days=i)] = z3.BitVec(f'_s{i}', 24)
            self.end_times[self.first_shift + timedelta(days=i)] = z3.BitVec(f'_e{i}', 24)

    def start_time(self, date):
        """Returns the start time of the shift"""
        return self.start_times[date]

    def end_time(self, date):
        """Returns the end time of the shift"""
        return self.end_times[date]

    def shift_length(self, date):
        """Returns the length of the shift"""
        return If(
            self.start_time(date) == NONE,
            ZERO,
            If(
                self.end_time(date) == NONE,
                self.end_time(date + DAYS_1) + HOURS_24 - self.start_time(date),
                self.end_time(date) - self.start_time(date)
            )
        )

    def is_long_shift(self, date):
        """Returns True if the shift is a long shift else False"""
        return self.shift_length(date) > HOURS_10

    def is_long_evening_shift(self, date):
        """Returns True if the shift is a long evening shift else False"""
        return And(self.start_time(date) < HOURS_16, self.end_time(date) > HOURS_23)

    def is_night_shift(self, date):
        """Returns True if the shift is a night shift else False"""
        return And(self.start_time(date) <= HOURS_23,
            self.start_time(date + DAYS_1) == NONE,
            self.end_time(date + DAYS_1) >= HOURS_6
        )

    def shift_time_constraints(self, date):
        """
        Shift times must be:
            • greater than or equal to 00:00
            • less than  24:00
            • divisible by 00:30
        Or:
            • Not a time (such as a day of rest or because the end of a shift is the following day)
        """
        return And(
            Or(
                And(
                    self.start_time(date) >= ZERO,
                    self.start_time(date) < HOURS_24,
                    self.start_time(date) % MINUTES_30 == ZERO,
                ),
                self.start_time(date) == NONE
            ),
            Or(
                And(
                    self.end_time(date) >= ZERO,
                    self.end_time(date) < HOURS_24,
                    self.end_time(date) % MINUTES_30 == ZERO,
                ),
                self.end_time(date) == NONE
            )
        )

    def shift_relationships_1(self, date):
        """
        Essentially, the only two conditions that follow on from if there is a start time:
            • the shift ends on the same day at a later time
            • the shift ends the next day
        """
        return If(
            self.start_time(date) != NONE,
            Xor(
                And(
                    self.end_time(date) != NONE,
                    self.end_time(date) > self.start_time(date)
                ),
                And(
                    self.start_time(date + DAYS_1) == NONE,
                    self.end_time(date + DAYS_1) != NONE
                )
            ),
            True
        )

    def shift_relationships_2(self, date):
        """
        Essentially, the only two conditions in which there is no start time is when:
            • it is a rest day
            • the previous days shift is ending on this day
        """
        return If(
            self.start_time(date) == NONE,
            Xor(
                self.end_time(date) == NONE,
                And(
                    self.start_time(date - DAYS_1) != NONE,
                    self.end_time(date - DAYS_1) == NONE,
                    self.end_time(date) != NONE
                )
            ),
            True
        )

    def last_shift_constraints(self):
        """If last shift has a start time then it must also have an end time."""
        return If(self.start_time(self.last_shift) != NONE, self.end_time(self.last_shift) == NONE, True)

    def first_shift_constraints(self):
        """If first shift has an end time then it must also have a start time."""
        return If(self.end_time(self.first_shift) != NONE, self.start_time(self.first_shift) != NONE, True)

    def average_working_week(self):
        """Returns the average working week in seconds"""
        return UDiv(
            z_sum([self.shift_length(self.first_shift + timedelta(days=i)) for i in range(self.length)]),
            BitVecVal((self.length * 86400) // 604800, 24)
        )

    def seven_prev_shifts(self, date):
        """Returns true if the previous seven days have been worked else False"""
        c = [self.start_time(date - timedelta(days=i)) != NONE for i in range(1, 8)]
        return And(c[0], c[1], c[2], c[3], c[4], c[5], c[6])

    def fourty_eight_hours_rest(self, date):
        """Returns True if there has been 48 hours of rest after the ending of this shift"""
        return And(
                self.start_time(date) == NONE,
                self.start_time(date + DAYS_1) == NONE,
                If(
                    self.end_time(date) == NONE,
                    And(
                        self.start_time(date + DAYS_2) == NONE,
                        self.start_time(date + DAYS_3) >= self.end_time(date)
                    ),
                    self.start_time(date + DAYS_2) >= self.end_time(date)
                )
            )

    def rest_after_night_shift(self, date):
        """If this shift is a night shift then there must be 46 hours of rest between the next shift"""
        return If(
            self.is_night_shift(date),
            And(
                self.start_time(date + DAYS_2) == NONE,
                self.start_time(date + DAYS_3) >= self.end_time(date + DAYS_1) - HOURS_2
            ),
            True
        )

    def long_shift_constraints(self, date):
        """48 hours of rest after four previous long shifts"""
        return If(four_prev_shifts(date, self.is_long_shift), self.rest_after_night_shift(date), True)

    def long_evening_shift_constraints(self, date):
        """48 hours of rest after four previous long evening shifts"""
        return If(four_prev_shifts(date, self.is_long_evening_shift), self.rest_after_night_shift(date), True)

    def night_shift_constraints(self, date):
        """No more than four consecutive night shifts"""
        return Not(
            And(
                four_prev_shifts(date, self.is_long_evening_shift),
                self.start_time(date + DAYS_1) != NONE
            )
        )

    def max_shifts(self, date):
        """48 hours rest after 7 consecutive days"""
        return If(self.seven_prev_shifts(date), self.fourty_eight_hours_rest(date), True)

    def weekend_constraints(self):
        """Returns a list of constraints, each one is True only if no more than 1 in 3 weekends have been worked."""
        weekends = []
        weekend_constraints = []
        for i in range(self.length):
            date = self.first_shift + timedelta(days=i)
            if is_sat(date):
                weekends.append(
                    Or(
                        self.start_time(date) != NONE,
                        self.end_time(date) != NONE,
                        self.start_time(date + DAYS_1) != NONE,
                        self.end_time(date + DAYS_1) != NONE
                    )
                )
        for i in range(len(weekends) - 2):
            weekend_constraints.append(
                Not(
                    And(
                        weekends[i],
                        weekends[i + 1],
                        weekends[i + 2]
                    )
                )
            )
        return weekend_constraints


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
        """

        # final three shifts are all rest days (these are included to prevent key errors)
        for i in range(self.rota.length, self.rota.length + 3):
            self.o.add(self.rota.start_time(self.rota.first_shift + timedelta(days=i)) == NONE)
            self.o.add(self.rota.end_time(self.rota.first_shift + timedelta(days=i)) == NONE)

        # add general shift time constraints and the first set of relationships between shift times
        for i in range(self.rota.length):
            self.o.add(self.rota.shift_time_constraints(self.rota.first_shift + timedelta(days=i)))
            self.o.add(self.rota.shift_relationships_1(self.rota.first_shift + timedelta(days=i)))

        # add the second set of relationships between shift times
        for i in range(1, self.rota.length):
            self.o.add(self.rota.shift_relationships_2(self.rota.first_shift + timedelta(days=i)))

        # add first and last shift constraints
        self.o.add(self.rota.last_shift_constraints())
        self.o.add(self.rota.first_shift_constraints())

        # max 48-hour average working week
        self.o.add(self.rota.average_working_week() <= BitVecVal(172800, 24))

        # max 72 hours work in any consecutive period of 168 hours
        """TO ADD"""

        # max 13-hour shift length
        for i in range(self.rota.length):
            self.o.add(self.rota.shift_length(self.rota.first_shift + timedelta(days=i)) <= BitVecVal(46800, 24))

        # 46 hours of rest required after any number of night shifts
        for i in range(self.rota.length - 1):
            self.o.add(self.rota.rest_after_night_shift(self.rota.first_shift + timedelta(days=i)))

        # adds long, long evening and night shift constraints
        for i in range(4, self.rota.length):
            self.o.add(self.rota.long_shift_constraints(self.rota.first_shift + timedelta(days=i)))
            self.o.add(self.rota.long_evening_shift_constraints(self.rota.first_shift + timedelta(days=i)))
            self.o.add(self.rota.night_shift_constraints(self.rota.first_shift + timedelta(days=i)))

        # maximum of 7 consecutive days worked
        for i in range(7, self.rota.length):
            self.o.add(self.rota.max_shifts(self.rota.first_shift + timedelta(days=i)))

        # max 1 in 3 weekends worked
        for constraint in self.rota.weekend_constraints():
            self.o.add(constraint)

    def evaluate(self):
        if self.o.check() == sat:
            m = self.o.model()
            return m
        else:
            return False


def convert_z3_ref(ref):
    ref = int(str(ref))
    if ref == 16777215:
        return -1
    else:
        return ref / 3600


def shift_times(l):
    n = len(l)
    ln = []
    for i in range(n):
        if l[i][0] == -1:
            ln.append(0)
        elif l[i][1] == -1:
            ln.append(l[i + 1][1] + 24 - l[i][0])
        else:
            ln.append(l[i][1] - l[i][0])
    return ln


def main():
    start_date = date(2023, 1, 1)
    end_date = date(2023, 7, 1)
    r = RotaCreator(start_date, end_date)
    r.set_constraints()
    m = r.evaluate()
    if m is False:
        print(m)
    else:
        weekday_dict = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday", 5: "Saturday",
                        6: "Sunday"}
        weekdays = [weekday_dict[calendar.weekday(date.year, date.month, date.day)] for date in
                    r.rota.start_times.keys()]
        starts = [convert_z3_ref(m[d]) for d in r.rota.start_times.values()]
        ends = [convert_z3_ref(m[d]) for d in r.rota.end_times.values()]
        starts_and_ends = [list(a) for a in zip(starts, ends)]
        shift_lengths = shift_times(starts_and_ends)
        for item in zip(weekdays, starts, ends, shift_lengths):
            print(f"{item[0]: <10} {item[1]: <10} {item[2]: <10} {item[3]: <10}")


if __name__ == '__main__':
    main()
