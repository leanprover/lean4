import Std.Time
open Std.Time


def ISO8601UTCAllow : GenericFormat .any := datespec("uuuu-MM-dd'T'HH:mm:ss.SSSSSSSSSZ", { allowLeapSeconds := true })
def ISO8601UTCNot : GenericFormat .any := datespec("uuuu-MM-dd'T'HH:mm:ss.SSSSSSSSSZ", { allowLeapSeconds := false })
def ISO8601UTCDef : GenericFormat .any := datespec("uuuu-MM-dd'T'HH:mm:ss.SSSSSSSSSZ")

/--
info: Except.ok (zoned("2002-07-14T23:14:00.324354679-23:59"))
-/
#guard_msgs in
#eval ISO8601UTCAllow.parse "2002-07-14T23:13:60.324354679-2359"

/--
info: Except.error "offset 19: need a natural number in the interval of 0 to 59"
-/
#guard_msgs in
#eval ISO8601UTCNot.parse "2002-07-14T23:13:60.324354679-2359"

/--
info: Except.error "offset 19: need a natural number in the interval of 0 to 59"
-/
#guard_msgs in
#eval ISO8601UTCDef.parse "2002-07-14T23:13:60.324354679-2359"

/-
Offset
-/

/--
info: Except.error "offset 32: invalid hour offset: 24. Must be between 0 and 23."
-/
#guard_msgs in
#eval ISO8601UTCAllow.parse "2002-07-14T23:14:00.324354679+2400"

/--
info: Except.error "offset 32: invalid hour offset: 99. Must be between 0 and 23."
-/
#guard_msgs in
#eval ISO8601UTCAllow.parse "2002-07-14T23:14:00.324354679+9900"

/--
info: Except.error "offset 34: invalid minute offset: 99. Must be between 0 and 59."
-/
#guard_msgs in
#eval ISO8601UTCAllow.parse "2002-07-14T23:14:00.324354679+0099"

/--
info: Except.ok (zoned("2002-07-14T23:14:00.324354679-23:59"))
-/
#guard_msgs in
#eval ISO8601UTCAllow.parse "2002-07-14T23:14:00.324354679-2359"

/--
info: Except.ok (zoned("2002-07-14T23:14:00.324354679+23:59"))
-/
#guard_msgs in
#eval ISO8601UTCAllow.parse "2002-07-14T23:14:00.324354679+2359"

/--
info: Except.error "offset 32: invalid hour offset: 24. Must be between 0 and 23."
-/
#guard_msgs in
#eval ISO8601UTCAllow.parse "2002-07-14T23:14:00.324354679-2400"

/--
info: Except.error "offset 32: invalid hour offset: 99. Must be between 0 and 23."
-/
#guard_msgs in
#eval ISO8601UTCAllow.parse "2002-07-14T23:14:00.324354679-9900"

/--
info: Except.error "offset 34: invalid minute offset: 99. Must be between 0 and 59."
-/
#guard_msgs in
#eval ISO8601UTCAllow.parse "2002-07-14T23:14:00.324354679-0099"
