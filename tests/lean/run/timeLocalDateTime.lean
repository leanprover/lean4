import Std.Time
import Init
open Std.Time

def ShortDateTime : Format .any := date-spec% "DD/MM/YYYY hh:mm:ss"
def ShortDate : Format .any := date-spec% "DD/MM/YYYY"
def format (localDate : LocalDateTime) : String := ShortDateTime.formatBuilder localDate.day localDate.month localDate.year localDate.time.hour localDate.minute localDate.time.second
def format₂ (localDate : LocalDate) : String := ShortDate.formatBuilder localDate.day localDate.month localDate.year

def date₁ := date% 1993-11-19:09:08:07
def date₂ := date% 1993-05-09:12:59:59
def date₃ := date% 2024-08-16
def date₄ := date% 1500-08-16

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
#eval date₁.toLocalTimestamp.toSeconds

/--
info: 736952399
-/
#guard_msgs in
#eval date₂.toLocalTimestamp.toSeconds

/--
info: "09/05/1993 12:59:59"
-/
#guard_msgs in
#eval LocalDateTime.ofUTCTimestamp 736952399 |> format

/--
info: 736952399
-/
#guard_msgs in
#eval LocalDateTime.toLocalTimestamp date₂ |>.toSeconds

/--
info: "16/08/2024"
-/
#guard_msgs in
#eval LocalDate.ofDaysSinceUNIXEpoch 19951 |> format₂

/--
info: 19951
-/
#guard_msgs in
#eval LocalDate.toDaysSinceUNIXEpoch date₃

/--
info: Std.Time.Weekday.friday
-/
#guard_msgs in
#eval LocalDate.weekday date₃


#eval Id.run do
  let mut res := #[]

  for i in [0:10000] do
    let i := Int.ofNat i - 999975
    let date := LocalDate.ofDaysSinceUNIXEpoch (Day.Offset.ofInt i)
    let num := date.toDaysSinceUNIXEpoch
    if i ≠ num.val then
      res := res.push i

  return res
