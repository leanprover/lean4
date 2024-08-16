import Std.Time
open Std.Time

def ShortDateTime : Format .any := date-spec% "DD/MM/YYYY hh:mm:ss"
def ShortDate : Format .any := date-spec% "DD/MM/YYYY"
def format (localDate : LocalDateTime) : String := ShortDateTime.formatBuilder localDate.day localDate.month localDate.year localDate.time.hour localDate.minute localDate.time.second
def format₂ (localDate : LocalDate) : String := ShortDate.formatBuilder localDate.day localDate.month localDate.year

def date₁ := date% 19-11-1993:09:08:07
def date₂ := date% 09-05-1993:12:59:59
def date₃ := date% 16-08-2024
def date₄ := date% 16-08-1500

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
info: Std.Time.Weekday.fri
-/
#guard_msgs in
#eval LocalDate.weekday date₃
