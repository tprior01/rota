from z3 import *
import calendar
from datetime import date, timedelta
from copy import deepcopy


def z_sum(z_list):
    """
    :param z_list: a list of z3.BitVecRef objects
    :type z_list: list[z3.BitVecRef]
    :return: the sum of the items in the list
    :rtype: z3.BitVecRef
    """
    s = 0
    for item in z_list:
        s += item
    return s


def is_sat(date):
    """
    :param date: the date to query
    :type date: date
    :return: True if the date is a Saturday else False
    :rtype: bool
    """
    return calendar.weekday(date.year, date.month, date.day) == 5


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
        for i in range(self.length, self.length + 3):
            self.start_times[self.start_date + timedelta(days=i)] = z3.BitVec(f'_s{i}', 24)
            self.end_times[self.start_date + timedelta(days=i)] = z3.BitVec(f'_e{i}', 24)

    def start_time(self, date):
        """
        :param date: the date of the shift
        :type date: date
        :return: the start time of the shift
        :rtype: z3.BitVecRef
        """
        return self.start_times[date]

    def end_time(self, date):
        """
        :param date: the date of the shift
        :type date: date
        :return: the end time of the shift
        :rtype: z3.BitVecRef
        """
        return self.end_times[date]

    def shift_length(self, date):
        """
        :param date: the date of the shift
        :type date: date
        :return: the shift length in seconds
        :rtype: z3.BitVecRef
        """
        return If(
            self.start_time(date) == BitVecVal(16777215, 24),
            BitVecVal(0, 24),
            If(
                self.end_time(date) == BitVecVal(16777215, 24),
                self.end_time(date + timedelta(days=1)) + z3.BitVecVal(86400, 24) - self.start_time(date),
                self.end_time(date) - self.start_time(date)
            )
        )

    def is_long_shift(self, date):
        """
        :param date: the date of the shift
        :type date: date
        :return: True if the shift is longer than 10 hours else False
        :rtype: z3.BitVecRef

        Notes:
            • 10hrs = 3600s
        """
        return self.shift_length(date) > BitVecVal(3600, 24)

    def is_long_evening_shift(self, date):
        """
        :param date: the date of the shift
        :type date: date
        :return: True if the shift starts before 16:00 and ends after 23:00 else False
        :rtype: z3.BitVecRef

        Notes:
            • 16:00 = 57600s
            • 23:00 = 82800s
        """
        return And(
            self.start_time(date) < BitVecVal(57600, 24),
            self.end_time(date) > BitVecVal(82800, 24)
        )

    def is_night_shift(self, date):
        """
        :param date: the date of the shift
        :type date: date
        :return: True if the shift starts before or at 23:00 and ends the next day on or after 06:00 else False
        :rtype: z3.BitVecRef

        Notes:
            • 23:00 = 82800s
            • 06:00 = 57600s
        """
        return And(
            self.start_time(date) <= BitVecVal(82800, 24),
            self.start_time(date + timedelta(days=1)) == BitVecVal(16777215, 24),
            self.end_time(date + timedelta(days=1)) >= BitVecVal(57600, 24)
        )

    def start_time_constraints(self, date):
        """
        :param date: the date of the shift
        :type date: date
        :return: a boolean representing the constraints for the start times of a shift
        :rtype: z3.BitVecRef

        Start times of a shift must be
            • greater than or equal to 00:00
            • less than  24:00
            • divisible by 00:30
            OR
            • where a shift does not start on this day, it is represented by the largest 24 bit number (16777215)
        """
        return Or(
            And(
                self.start_time(date) >= BitVecVal(0, 24),
                self.start_time(date) < BitVecVal(86400, 24),
                self.start_time(date) % BitVecVal(1800, 24) == BitVecVal(0, 24),
            ),
            self.start_time(date) == BitVecVal(16777215, 24)
        )

    def end_time_constraints(self, date):
        """
        :param date: the date of the shift
        :type date: date
        :return: a boolean representing the constraints for the end times of a shift
        :rtype: z3.BitVecRef

        End times of a shift must be
            • if th
            • greater than or equal to 00:00
            • less than  24:00
            • divisible by 00:30
            OR
            • where a shift does not start on this day, it is represented by the largest 24 bit number (16777215)
        """
        return Or(
            And(
                self.end_time(date) >= BitVecVal(0, 24),
                self.end_time(date) < BitVecVal(86400, 24),
                self.end_time(date) % BitVecVal(1800, 24) == BitVecVal(0, 24),
            ),
            self.end_time(date) == BitVecVal(16777215, 24)
        )

    def shift_relationship_constraints_1(self, date):
        """
        :param date: the date of the shift
        :type date: date
        :return: a boolean representing the constraints where there are rest days
        :rtype: z3.BitVecRef

        If there is a start time for a shift then:
            • the end time for that shift must be on the same day
            OR
            • the end time for that shift will be the next day
            • and there will be no start time for the
        """
        return If(
            self.start_time(date) != BitVecVal(16777215, 24),
            Xor(
                And(
                    self.end_time(date) != BitVecVal(16777215, 24),
                    self.end_time(date) > self.start_time(date)
                ),
                And(
                    self.start_time(date + timedelta(days=1)) == BitVecVal(16777215, 24),
                    self.end_time(date + timedelta(days=1)) != BitVecVal(16777215, 24)
                )
            ),
            True
        )

    def shift_relationship_constraints_2(self, date):
        """
        :param date: the date of the shift
        :type date: date
        :return: a boolean representing the constraints where there are rest days
        :rtype: z3.BitVecRef

        If there is a start time for a shift then:
            • the end time for that shift must be on the same day
            OR
            • the end time for that shift will be the next day
            • and there will be no start time for the
        """
        return If(
            self.start_time(date) == BitVecVal(16777215, 24),
            Xor(
                self.end_time(date) == BitVecVal(16777215, 24),
                And(
                    self.start_time(date - timedelta(days=1)) != BitVecVal(16777215, 24),
                    self.end_time(date - timedelta(days=1)) == BitVecVal(16777215, 24),
                    self.end_time(date) != BitVecVal(16777215, 24)
                )
            ),
            True
        )

    def last_shift_constraints(self):
        """
        :return: a boolean representing the constraints for the last shift in the rota
        :rtype: z3.BitVecRef

        If last shift has a start time then it must also have an end time.
        """
        return If(
            self.start_time(self.last_shift) != BitVecVal(16777215, 24),
            self.end_time(self.last_shift) == BitVecVal(16777215, 24),
            True
        )

    def first_shift_constraints(self):
        """
        :return: a boolean representing the constraints for the last shift in the rota
        :rtype: z3.BitVecRef

        If first shift has an end time then it must also have a start time.
        """
        return If(
            self.end_time(self.start_date) != BitVecVal(16777215, 24),
            self.start_time(self.start_date) != BitVecVal(16777215, 24),
            True
        )

    def average_working_week(self):
        """
        :return: the average working week in seconds
        :rtype: z3.BitVecRef

        Notes:
            • 1 day = 86400s
            • 7 days = 604800s
        """
        return UDiv(
            z_sum([self.shift_length(self.start_date + timedelta(days=i)) for i in range(self.length)]),
            BitVecVal((self.length * 86400) // 604800, 24)
        )

    def four_prev_long_shifts(self, date):
        """
        :param date: the date of the shift
        :type date: date
        :return: true if the previous four shifts were long shifts else false
        :rtype: z3.BitVecRef
        """
        return And(
            self.is_long_shift(date - timedelta(days=4)),
            self.is_long_shift(date - timedelta(days=3)),
            self.is_long_shift(date - timedelta(days=2)),
            self.is_long_shift(date - timedelta(days=1))
        )

    def four_prev_long_evening_shifts(self, date):
        """
        :param date: the date of the shift
        :type date: date
        :return: true if the previous four shifts were long evening shifts else false
        :rtype: z3.BitVecRef
        """
        return And(
            self.is_long_evening_shift(date - timedelta(days=4)),
            self.is_long_evening_shift(date - timedelta(days=3)),
            self.is_long_evening_shift(date - timedelta(days=2)),
            self.is_long_evening_shift(date - timedelta(days=1))
        )

    def four_prev_night_shifts(self, date):
        """
        :param date: the date of the shift
        :type date: date
        :return: true if the previous four shifts were night shifts else false
        :rtype: z3.BitVecRef
        """
        return And(
            self.is_night_shift(date - timedelta(days=4)),
            self.is_night_shift(date - timedelta(days=3)),
            self.is_night_shift(date - timedelta(days=2)),
            self.is_night_shift(date - timedelta(days=1))
        )

    def seven_prev_shifts(self, date):
        return And(
            self.start_time(date - timedelta(days=1)) != BitVecVal(16777215, 24),
            self.start_time(date - timedelta(days=2)) != BitVecVal(16777215, 24),
            self.start_time(date - timedelta(days=3)) != BitVecVal(16777215, 24),
            self.start_time(date - timedelta(days=4)) != BitVecVal(16777215, 24),
            self.start_time(date - timedelta(days=5)) != BitVecVal(16777215, 24),
            self.start_time(date - timedelta(days=6)) != BitVecVal(16777215, 24),
            self.start_time(date - timedelta(days=7)) != BitVecVal(16777215, 24),
        )

    def rest_after_night_shift(self, date):
        """
        :param date: the date of the shift
        :type date: date
        :return: a boolean representing the combination of constraints for rest after a night shift
        :rtype: z3.BitVecRef

        These constraints are applied to all shifts apart from the final, as the final shift cannot be a night shift.
        """
        return Not(
            And(
                self.is_night_shift(date),
                self.start_time(date + timedelta(days=2)) != BitVecVal(16777215, 24),
                self.start_time(date + timedelta(days=3)) < self.end_time(date + timedelta(days=1)) -
                BitVecVal(7200, 24)
            )
        )

    def rest_after_long_shifts(self, date):
        """
        :param date: the date of the shift
        :type date: date
        :return: a boolean representing the constraints for rest after four long shifts
        :rtype: z3.BitVecRef
        """
        return Not(
            And(
                self.four_prev_long_shifts(date),
                self.start_time(date) != BitVecVal(16777215, 24),
                self.start_time(date + timedelta(days=1)) != BitVecVal(16777215, 24),
                If(
                    self.end_time(date) == BitVecVal(16777215, 24),
                    And(
                        self.start_time(date + timedelta(days=2)) != BitVecVal(16777215, 24),
                        self.start_time(date + timedelta(days=3)) < self.end_time(date)
                    ),
                    self.start_time(date + timedelta(days=2)) < self.end_time(date)
                )
            )
        )

    def rest_after_long_evening_shifts(self, date):
        """
        :param date: the date of the shift
        :type date: date
        :return: a boolean representing the constraints for rest after four long shifts
        :rtype: z3.BitVecRef
        """
        return Not(
            And(
                self.four_prev_night_shifts(date),
                self.is_night_shift(date)
            )
        )

    def max_night_shifts(self, date):
        """
        :param date: the date of the shift
        :type date: date
        :return: a boolean representing ...
        :rtype: z3.BitVecRef
        """
        return Not(
            And(
                self.four_prev_long_evening_shifts(date),
                self.start_time(date) != BitVecVal(16777215, 24),
                self.start_time(date + timedelta(days=1)) != BitVecVal(16777215, 24),
                If(
                    self.end_time(date) == BitVecVal(16777215, 24),
                    And(
                        self.start_time(date + timedelta(days=2)) != BitVecVal(16777215, 24),
                        self.start_time(date + timedelta(days=3)) < self.end_time(date)
                    ),
                    self.start_time(date + timedelta(days=2)) < self.end_time(date)
                )
            )
        )

    def max_shifts(self, date):
        """
        :param date: the date of the shift
        :type date: date
        :return: a boolean representing ...
        :rtype: z3.BitVecRef
        """
        return Not(
            And(
                self.seven_prev_shifts(date),
                self.start_time(date) != BitVecVal(16777215, 24),
                self.start_time(date + timedelta(days=1)) != BitVecVal(16777215, 24),
                If(
                    self.end_time(date) == BitVecVal(16777215, 24),
                    And(
                        self.start_time(date + timedelta(days=2)) != BitVecVal(16777215, 24),
                        self.start_time(date + timedelta(days=3)) < self.end_time(date)
                    ),
                    self.start_time(date + timedelta(days=2)) < self.end_time(date)
                )
            )
        )

    def weekend_constraints(self):
        weekends = []
        weekend_constraints = []
        for i in range(self.length):
            date = self.start_date + timedelta(days=i)
            if is_sat(date):
                weekends.append(
                    Or(
                        self.start_time(date) != BitVecVal(16777215, 24),
                        self.end_time(date) != BitVecVal(16777215, 24),
                        self.start_time(date + timedelta(days=1)) != BitVecVal(16777215, 24),
                        self.end_time(date + timedelta(days=1)) != BitVecVal(16777215, 24)
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

        Alongside are additional constraints:
            • end times must be greater than start times, unless there is no start time
            • start and end times must be greater than or equal to 00:00 and less than 24:00
            • the final shift cannot be a night shift
            • three additional rest shifts are added which are all rest days, to prevent key errors
            • if there is no
        """

        # final three shifts are all rest days (these are included to prevent key errors)
        for i in range(self.rota.length, self.rota.length + 3):
            self.o.add(self.rota.start_time(self.rota.start_date + timedelta(days=i)) == BitVecVal(16777215, 24))
            self.o.add(self.rota.end_time(self.rota.start_date + timedelta(days=i)) == BitVecVal(16777215, 24))

        for i in range(self.rota.length):
            # add general shift start time constraints
            self.o.add(self.rota.start_time_constraints(self.rota.start_date + timedelta(days=i)))
            # add general shift end time constraints
            self.o.add(self.rota.end_time_constraints(self.rota.start_date + timedelta(days=i)))
            # add relationships between shift constraints (1)
            self.o.add(self.rota.shift_relationship_constraints_1(self.rota.start_date + timedelta(days=i)))

        # add relationships between shift constraints (2)
        for i in range(1, self.rota.length):
            self.o.add(self.rota.shift_relationship_constraints_2(self.rota.start_date + timedelta(days=i)))

        # add last shift constraints
        self.o.add(self.rota.last_shift_constraints())

        # add first shift constraints
        self.o.add(self.rota.first_shift_constraints())

        # max 48-hour average working week
        self.o.add(self.rota.average_working_week() <= BitVecVal(172800, 24))

        # max 72 hours work in any consecutive period of 168 hours
        """TO ADD"""

        for i in range(self.rota.length):
            # max 13-hour shift length
            self.o.add(self.rota.shift_length(self.rota.start_date + timedelta(days=i)) <= BitVecVal(46800, 24))

        for i in range(self.rota.length - 1):
            # 46 hours of rest required after any number of night shifts
            self.o.add(self.rota.rest_after_night_shift(self.rota.start_date + timedelta(days=i)))

        for i in range(4, self.rota.length):
            # max 4 consecutive long shifts, at least 48 hours rest following the fourth shift
            self.o.add(self.rota.rest_after_long_shifts(self.rota.start_date + timedelta(days=i)))
            # max 4 consecutive long evening shifts, at least 48 hours rest following the fourth shift
            self.o.add(self.rota.rest_after_long_evening_shifts(self.rota.start_date + timedelta(days=i)))
            # max 4 consecutive night shifts
            self.o.add(self.rota.max_night_shifts(self.rota.start_date + timedelta(days=i)))

        for i in range(7, self.rota.length):
            self.o.add(self.rota.max_shifts(self.rota.start_date + timedelta(days=i)))

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
