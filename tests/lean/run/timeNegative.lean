import Std.Time
import Init
open Std.Time

/--
info: Timestamp.ofNanosecondsSinceUnixEpoch -999999999
-/
#guard_msgs in
#eval datetime("1969-12-31T23:59:59.000000001").toTimestampAssumingUTC

/--
info: Timestamp.ofNanosecondsSinceUnixEpoch -1000000000
-/
#guard_msgs in
#eval datetime("1969-12-31T23:59:59.000000000").toTimestampAssumingUTC

/--
info: datetime("1969-12-31T23:59:59.000000001")
-/
#guard_msgs in
#eval datetime("1969-12-31T23:59:59.000000001").toTimestampAssumingUTC.toPlainDateTimeAssumingUTC

/--
info: datetime("1969-12-31T23:59:59.000000000")
-/
#guard_msgs in
#eval datetime("1969-12-31T23:59:59.000000000").toTimestampAssumingUTC.toPlainDateTimeAssumingUTC

/--
info: datetime("1969-12-31T23:59:59.000000001")
-/
#guard_msgs in
#eval datetime("1969-12-31T23:59:59.000000000") + (1 : Nanosecond.Offset)

/--
info: datetime("1970-01-01T00:00:00.000000000")
-/
#guard_msgs in
#eval datetime("1969-12-31T23:59:59.999999999") + (1 : Nanosecond.Offset)

/--
info: datetime("1970-01-01T00:00:01.000000000")
-/
#guard_msgs in
#eval datetime("1970-01-01T00:00:00.999999999") + (1 : Nanosecond.Offset)

/--
info: Timestamp.ofNanosecondsSinceUnixEpoch -1
-/
#guard_msgs in
#eval datetime("1969-12-31T23:59:59.999999999").toTimestampAssumingUTC

/--
info: Timestamp.ofNanosecondsSinceUnixEpoch 0
-/
#guard_msgs in
#eval datetime("1969-12-31T23:59:59.999999999").toTimestampAssumingUTC + (1 : Nanosecond.Offset)


/--
info: datetime("1970-01-01T00:00:00.000000000")
-/
#guard_msgs in
#eval PlainDateTime.ofTimestampAssumingUTC 0

/--
info: 121
-/
#guard_msgs in
#eval datetime("1804-04-30T23:59:59.999999999").dayOfYear

/--
info: 35
-/
#guard_msgs in
#eval datetime("1906-08-27T23:59:59.999999999").weekOfYear

/--
info: datetime("1906-08-27T23:59:59.999999999")
-/
#guard_msgs in
#eval datetime("1906-08-27T23:59:59.999999999").toTimestampAssumingUTC.toPlainDateTimeAssumingUTC
