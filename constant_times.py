from datetime import timedelta
from z3 import BitVecVal

NA = BitVecVal(511, 9)
DAYS_1 = timedelta(days=1)
DAYS_2 = timedelta(days=2)
DAYS_3 = timedelta(days=3)
HOURS_0 = BitVecVal(0, 9)
HOURS_2 = BitVecVal(4, 9)
HOURS_3 = BitVecVal(6, 9)
HOURS_6 = BitVecVal(12, 9)
HOURS_9 = BitVecVal(18, 9)
HOURS_10 = BitVecVal(20, 9)
HOURS_11 = BitVecVal(22, 9)
HOURS_13 = BitVecVal(26, 9)
HOURS_16 = BitVecVal(32, 9)
HOURS_20 = BitVecVal(40, 9)
HOURS_23 = BitVecVal(46, 9)
HOURS_24 = BitVecVal(48, 9)
HOURS_26 = BitVecVal(52,9)
HOURS_48 = BitVecVal(96, 9)
HOURS_72 = BitVecVal(144, 9)
MINS_30 = BitVecVal(1, 9)

HOURS_8_MINS_30 = BitVecVal(17, 9)
HOURS_21_MINS_30 = BitVecVal(43, 9)
