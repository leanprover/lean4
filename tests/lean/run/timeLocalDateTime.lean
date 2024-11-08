import Std.Time
import Init
open Std.Time

def ShortDateTime : GenericFormat .any := datespec("dd/MM/uuuu HH:mm:ss")
def ShortDate : GenericFormat .any := datespec("dd/MM/uuuu")

def format (PlainDate : PlainDateTime) : String := ShortDateTime.formatBuilder PlainDate.day PlainDate.month PlainDate.year PlainDate.time.hour PlainDate.minute PlainDate.time.second
def format₂ (PlainDate : PlainDate) : String := ShortDate.formatBuilder PlainDate.day PlainDate.month PlainDate.year

def date₁ := datetime("1993-11-19T09:08:07")
def date₂ := datetime("1993-05-09T12:59:59")
def date₃ := date("2024-08-16")
def date₄ := date("1500-08-16")

def tm₁ := 753700087
def tm₂ := 736952399

/--
info: "19/11/1993 09:08:07"
-/
#guard_msgs in
#eval format date₁

/--
info: "09/05/1993 12:59:59"
-/
#guard_msgs in
#eval format date₂

/--
info: 753700087
-/
#guard_msgs in
#eval date₁.toTimestampAssumingUTC.toSecondsSinceUnixEpoch

/--
info: 736952399
-/
#guard_msgs in
#eval date₂.toTimestampAssumingUTC.toSecondsSinceUnixEpoch

/--
info: "09/05/1993 12:59:59"
-/
#guard_msgs in
#eval PlainDateTime.ofTimestampAssumingUTC 736952399 |> format

/--
info: 736952399
-/
#guard_msgs in
#eval PlainDateTime.toTimestampAssumingUTC date₂ |>.toSecondsSinceUnixEpoch

/--
info: "16/08/2024"
-/
#guard_msgs in
#eval PlainDate.ofDaysSinceUNIXEpoch 19951 |> format₂

/--
info: 19951
-/
#guard_msgs in
#eval PlainDate.toDaysSinceUNIXEpoch date₃

/--
info: Std.Time.Weekday.friday
-/
#guard_msgs in
#eval PlainDate.weekday date₃

/--
info: #[]
-/
#guard_msgs in
#eval Id.run do
  let mut res := #[]

  for i in [0:10000] do
    let i := Int.ofNat i - 999975
    let date := PlainDate.ofDaysSinceUNIXEpoch (Day.Offset.ofInt i)
    let num := date.toDaysSinceUNIXEpoch
    if i ≠ num.val then
      res := res.push i

  return res
