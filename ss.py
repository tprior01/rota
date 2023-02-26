from z3 import *
import calendar
from datetime import date
from constant_times import *

# -*- coding: utf-8 -*-
"""
For rota rules see: https://www.nhsemployers.org/system/files/media/Rota-rules-at-a-glance_0.pdf 
"""


def z_sum(z_list):
    """Sums a list of BitVecRef types and returns a BitVecRef. This is a z3 compatible sum."""
    s = 0
    for item in z_list:
        s += item
    return s


def convert_z3_ref(ref):
    """
    Converts a BitVecRef to a decimal time. Shift times are represented in 30 min intervals, therefore to convert to
    decimal the solved BitVecRef is converted to an int then divided by two.
    """
    return int(str(ref)) / 2


def print_shift(start, end, length):
    """
    Prints formatted shift information. Non start times (represented as 255.5 after conversion) and shift lengths of 0
    are omitted.
    """
    start = start if start != 255.5 else ""
    end = end if end != 255.5 else ""
    length = length if length != 0 else ""
    return print(f"{start: <7}{end: <7}{length: <7}｜", end="")


def is_sat(date):
    """True of the date is a Saturday"""
    return calendar.weekday(date.year, date.month, date.day) == 5


def prev_shifts(date, bool_function, number):
    """
    Takes a function which has date as argument and outputs a Boolean (can be a Python bool or a BitVecRef). It checks
    if the function is True on any number of previous days. It returns a boolean BitVecRef which is True if the function
    returns True on each of those previous days."""
    return And([bool_function(date - timedelta(days=i)) for i in range(1, number + 1)])


class IndividualRota:
    def __init__(self, start_date, end_date, n):
        """
        :param start_date: the start date of the rota
        :type start_date: date
        :param end_date: the end date of the rota
        :type end_date: date
        :param n: a unique identifier for the rota
        :type n: int
        """
        self.first_shift = start_date
        self.last_shift = end_date - DAYS_1
        self.length = (end_date - start_date).days
        self.start_times = {start_date + timedelta(days=i): z3.BitVec(f's_{n}_{i}', 9) for i in range(self.length)}
        self.end_times = {start_date + timedelta(days=i): z3.BitVec(f'e_{n}_{i}', 9) for i in range(self.length)}
        for i in range(self.length, self.length + 3):
            self.start_times[self.first_shift + timedelta(days=i)] = z3.BitVec(f'_s{i}', 9)
            self.end_times[self.first_shift + timedelta(days=i)] = z3.BitVec(f'_e{i}', 9)

    def start_time(self, date):
        """Returns the start time of the shift"""
        return self.start_times[date]

    def end_time(self, date):
        """Returns the end time of the shift"""
        return self.end_times[date]

    def shift_length(self, date):
        """Returns the length of the shift"""
        return If(
            self.start_time(date) == NA,
            HOURS_0,
            If(
                self.end_time(date) == NA,
                self.end_time(date + DAYS_1) + HOURS_24 - self.start_time(date),
                self.end_time(date) - self.start_time(date)
            )
        )

    def shift_worked(self, date):
        """True if a there is a shift on this date"""
        return self.start_time(date) != NA

    def is_long_shift(self, date):
        """True if the shift is a long shift else False"""
        return self.shift_length(date) > HOURS_10

    def is_long_eve_shift(self, date):
        """True if the shift is a long evening shift else False"""
        return And(self.start_time(date) < HOURS_16, self.end_time(date) > HOURS_23)

    """
    BELOW INCORRECT
    """

    def is_night_shift(self, date):
        """True if the shift is a night shift else False"""
        return Or(
            self.start_time(date) + self.shift_length(date) >= HOURS_26,
            And(
                self.start_time(date) != NA,
                self.end_time(date) != NA,
                HOURS_6 - self.shift_length(date) - self.end_time(date) >= HOURS_3,
            )
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
                    self.start_time(date) >= HOURS_0,
                    self.start_time(date) < HOURS_24,
                    self.start_time(date) % MINS_30 == HOURS_0,
                ),
                self.start_time(date) == NA
            ),
            Or(
                And(
                    self.end_time(date) >= HOURS_0,
                    self.end_time(date) < HOURS_24,
                    self.end_time(date) % MINS_30 == HOURS_0,
                ),
                self.end_time(date) == NA
            )
        )

    def shift_relationships_1(self, date):
        """
        Essentially, the only two conditions that follow on from if there is a start time:
            • the shift ends on the same day at a later time
            • the shift ends the next day
        """
        return If(
            self.start_time(date) != NA,
            Xor(
                And(
                    self.end_time(date) != NA,
                    self.end_time(date) > self.start_time(date)
                ),
                And(
                    self.start_time(date + DAYS_1) == NA,
                    self.end_time(date + DAYS_1) != NA
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
            self.start_time(date) == NA,
            Xor(
                self.end_time(date) == NA,
                And(
                    self.start_time(date - DAYS_1) != NA,
                    self.end_time(date - DAYS_1) == NA,
                    self.end_time(date) != NA
                )
            ),
            True
        )

    def last_shift_constraints(self):
        """If last shift has a start time then it must also have an end time."""
        return If(self.start_time(self.last_shift) != NA, self.end_time(self.last_shift) == NA, True)

    def first_shift_constraints(self):
        """If first shift has an end time then it must also have a start time."""
        return If(self.end_time(self.first_shift) != NA, self.start_time(self.first_shift) != NA, True)

    def average_working_week(self):
        """Returns the average working week in seconds"""
        return UDiv(
            z_sum([self.shift_length(self.first_shift + timedelta(days=i)) for i in range(self.length)]),
            BitVecVal((self.length * 48) // 336, 9)
        )

    def fourty_eight_hours_rest(self, date):
        """Returns True if there has been 48 hours of rest after the ending of this shift"""
        return And(
            self.start_time(date) == NA,
            self.start_time(date + DAYS_1) == NA,
            If(
                self.end_time(date) == NA,
                And(
                    self.start_time(date + DAYS_2) == NA,
                    # this includes no start time, as this is represented by the maximum 9-bit number
                    self.start_time(date + DAYS_3) >= self.end_time(date)
                ),
                self.start_time(date + DAYS_2) >= self.end_time(date)
            )
        )

    def rest_after_night_shift(self, date):
        """If this shift is a night shift then there must be 46 hours of rest between the next shift"""
        return If(
            self.is_night_shift(date),
            Xor(
                self.is_night_shift(date + DAYS_1),
                And(
                    self.start_time(date + DAYS_2) == NA,
                    # this includes no start time, as this is represented by the maximum 9-bit number
                    self.start_time(date + DAYS_3) >= self.end_time(date + DAYS_1) - HOURS_2
                )
            ),
            True
        )

    def long_shift_constraints(self, date):
        """48 hours of rest after four previous long shifts"""
        return If(prev_shifts(date, self.is_long_shift, 4), self.fourty_eight_hours_rest(date), True)

    def long_eve_shift_constraints(self, date):
        """48 hours of rest after four previous long evening shifts"""
        return If(prev_shifts(date, self.is_long_eve_shift, 4), self.fourty_eight_hours_rest(date), True)

    def max_shifts(self, date):
        """48 hours rest after 7 consecutive days"""
        return If(prev_shifts(date, self.shift_worked, 7), self.fourty_eight_hours_rest(date), True)

    def max_night_shifts(self, date):
        """No more than four consecutive night shifts"""
        return If(
            prev_shifts(date, self.is_night_shift, 4),
            Not(
                self.is_night_shift(date)
            ),
            True
        )

    def max_72_hours_in_a_week(self, date):
        """max 72 hours worked """
        return z_sum([self.shift_length(date - timedelta(days=i)) for i in range(7)]) <= HOURS_72

    def weekend_constraints(self):
        """Returns a list of constraints, each one is True only if no more than 1 in 3 weekends have been worked."""
        weekends = []
        weekend_constraints = []
        for i in range(self.length):
            date = self.first_shift + timedelta(days=i)
            if is_sat(date):
                weekends.append(
                    Or(
                        self.start_time(date) != NA,
                        self.end_time(date) != NA,
                        self.start_time(date + DAYS_1) != NA,
                        self.end_time(date + DAYS_1) != NA
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

    def eleven_hours_rest(self, date):
        return If(
            self.end_time(date) != NA,
            self.start_time(date + DAYS_1) >= HOURS_24 - self.end_time(date) - HOURS_11,
            True
        )

    def add_constraints(self, o):
        """adds all constraints to an Optimize object"""
        # final three shifts are all rest days (these are included to prevent key errors)
        o.add([self.start_time(self.first_shift + timedelta(days=i)) == NA for i in range(self.length, self.length+3)])
        o.add([self.end_time(self.first_shift + timedelta(days=i)) == NA for i in range(self.length, self.length+3)])

        # add general shift time constraints and the relationships between shift times
        o.add([self.shift_time_constraints(self.first_shift + timedelta(days=i)) for i in range(self.length)])
        o.add([self.shift_relationships_1(self.first_shift + timedelta(days=i)) for i in range(self.length)])
        o.add([self.shift_relationships_2(self.first_shift + timedelta(days=i)) for i in range(1, self.length)])

        # add first and last shift constraints
        o.add(self.last_shift_constraints())
        o.add(self.first_shift_constraints())

        # max 48-hour average working week
        o.add(self.average_working_week() <= HOURS_48)

        # max 72 hours work in any consecutive period of 168 hours
        o.add([self.max_72_hours_in_a_week(self.first_shift + timedelta(days=i)) for i in range(7, self.length)])

        # max 13-hour shift length
        o.add([self.shift_length(self.first_shift + timedelta(days=i)) <= HOURS_13 for i in range(self.length)])

        # 46 hours of rest required after any number of night shifts
        o.add([self.rest_after_night_shift(self.first_shift + timedelta(days=i)) for i in range(self.length-1)])

        # adds long, long evening and night shift constraints
        o.add([self.long_shift_constraints(self.first_shift + timedelta(days=i)) for i in range(4, self.length)])
        o.add([self.long_eve_shift_constraints(self.first_shift + timedelta(days=i)) for i in range(4, self.length)])
        o.add([self.max_night_shifts(self.first_shift + timedelta(days=i)) for i in range(4, self.length)])

        # maximum of 7 consecutive days worked
        o.add([self.max_shifts(self.first_shift + timedelta(days=i)) for i in range(7, self.length)])

        # max 1 in 3 weekends worked
        o.add([constraint for constraint in self.weekend_constraints()])

        # nominally 11 hours rest between shifts
        o.add_soft([self.eleven_hours_rest(self.first_shift + timedelta(days=i)) for i in range(self.length)])


class RotaCreator:
    def __init__(self, start_date, end_date, no_people):
        """
        :param start_date: the start date of the rota
        :type start_date: date
        :param end_date: the end date of the rota
        :type end_date: date
        :param no_people: the number of people to work the rota
        :type no_people: int
        """
        self.no_people = no_people
        self.model = None
        self.c_starts = None
        self.c_ends = None
        self.c_lens = []
        self.rotas = [IndividualRota(start_date, end_date, i) for i in range(no_people)]
        self.length = (end_date - start_date).days
        self.first_shift = start_date
        self.last_shift = end_date - DAYS_1
        self.o = Optimize()
        for rota in self.rotas:
            rota.add_constraints(self.o)

        self.o.add([self.one_long_shift(self.first_shift + timedelta(days=i)) for i in range(self.length-1)])
        self.o.add([self.one_night_shift(self.first_shift + timedelta(days=i)) for i in range(7, self.length-7)])

    def one_long_shift(self, date):
        c = []
        for rota in self.rotas:
            c.append(
                And(
                    rota.start_time(date) <= HOURS_8_MINS_30,
                    rota.end_time(date) >= HOURS_21_MINS_30
                )
            )
        return Or(c)

    def one_night_shift(self, date):
        c = []
        for rota in self.rotas:
            c.append(
                And(
                    rota.start_time(date) <= HOURS_20,
                    rota.start_time(date + DAYS_1) == NA,
                    rota.end_time(date + DAYS_1) >= HOURS_9
                )
            )
        return Or(c)

    def evaluate(self):
        if self.o.check() == sat:
            self.model = self.o.model()
            self.c_starts = [[convert_z3_ref(self.model[r]) for r in rota.start_times.values()] for rota in self.rotas]
            self.c_ends = [[convert_z3_ref(self.model[r]) for r in rota.end_times.values()] for rota in self.rotas]
            for i in range(self.no_people):
                l = [list(z) for z in zip(self.c_starts[i], self.c_ends[i])]
                ln = []
                for i in range(len(l)):
                    if l[i][0] == 255.5:
                        ln.append(0)
                    elif l[i][1] == 255.5:
                        ln.append(l[i + 1][1] + 24 - l[i][0])
                    else:
                        ln.append(l[i][1] - l[i][0])
                self.c_lens.append(ln)

    def print_rota(self):
        if self.model is not None:
            print(f"{'':<20}", end="")
            for i in range(self.no_people):
                person = f"person {i}"
                print(f"｜{person:^21}", end="")
            print("｜")
            print(f"{'':<20}", end="")
            for i in range(self.no_people):
                print(f"｜{'start':<7}{'end':<7}{'length':<7}", end="")
            print("｜")
            for key, i in zip(self.rotas[0].start_times.keys(), range(self.rotas[0].length)):
                day = calendar.day_name[key.weekday()]
                date = key.strftime("%d/%m/%Y")
                print(f"{day: <10}{date: >10}｜", end="")
                for j in range(len(self.rotas)):
                    print_shift(self.c_starts[j][i], self.c_ends[j][i], self.c_lens[j][i])
                print()
        else:
            print("model unsat")


def main():
    r = RotaCreator(start_date=date(2023, 1, 1), end_date=date(2023, 7, 1), no_people=4)
    r.evaluate()
    r.print_rota()


if __name__ == '__main__':
    main()
