import Std.Time
open Std.Time

def brTZ : TimeZone := timezone("America/Sao_Paulo -03:00")
def date₁ := zoned("2014-06-16T03:03:03-03:00")

/--
info: "Monday, June 16, 2014 06:03:03"
-/
#guard_msgs in
#eval Formats.longDateFormat.format date₁.toDateTime

def tm := date₁.toTimestamp
def date₂ := DateTime.ofTimestamp tm brTZ

/--
info: "2014-06-16T03:03:03-03:00"
-/
#guard_msgs in
#eval Formats.iso8601.format date₂

/--
info: "06-16-2014"
-/
#guard_msgs in
#eval Formats.americanDate.format date₂

/--
info: "16-06-2014"
-/
#guard_msgs in
#eval Formats.europeanDate.format date₂

/--
info: "03:03:03 AM"
-/
#guard_msgs in
#eval Formats.time12Hour.format date₂

/--
info: "03:03:03"
-/
#guard_msgs in
#eval Formats.time24Hour.format date₂

/--
info: "2014-06-16:06:03:03.000000000"
-/
#guard_msgs in
#eval Formats.dateTime24Hour.format date₂

/--
info: "2014-06-16T03:03:03.000000000-0300"
-/
#guard_msgs in
#eval Formats.dateTimeWithZone.format date₂

/--
info: "03:03:03.000000000"
-/
#guard_msgs in
#eval Formats.leanTime24Hour.format date₂

/--
info: "03:03:03"
-/
#guard_msgs in
#eval Formats.leanTime24HourNoNanos.format date₂

/--
info: "2014-06-16T06:03:03.000000000"
-/
#guard_msgs in
#eval Formats.leanDateTime24Hour.format date₂

/--
info: "2014-06-16T06:03:03"
-/
#guard_msgs in
#eval Formats.leanDateTime24HourNoNanos.format date₂

/--
info: "2014-06-16T03:03:03.000000000-03:00"
-/
#guard_msgs in
#eval Formats.leanDateTimeWithZone.format date₂

/--
info: "2014-06-16T03:03:03-03:00"
-/
#guard_msgs in
#eval Formats.leanDateTimeWithZoneNoNanos.format date₂

/--
info: "2014-06-16T03:03:03[America/Sao_Paulo]"
-/
#guard_msgs in
#eval Formats.leanDateTimeWithIdentifier.format date₂

/--
info: "2014-06-16T03:03:03.000000000[America/Sao_Paulo]"
-/
#guard_msgs in
#eval Formats.leanDateTimeWithIdentifierAndNanos.format date₂

/--
info: "2014-06-16"
-/
#guard_msgs in
#eval Formats.leanDate.format date₂

/--
info: "2014-06-16"
-/
#guard_msgs in
#eval Formats.sqlDate.format date₂

/--
info: "Monday, June 16, 2014 06:03:03"
-/
#guard_msgs in
#eval Formats.longDateFormat.format date₂

/--
info: "Mon Jun 16 06:03:03 2014"
-/
#guard_msgs in
#eval Formats.ascTime.format date₂

/--
info: "Mon, 16 Jun 2014 03:03:03 -0300"
-/
#guard_msgs in
#eval Formats.rfc822.format date₂

/--
info: "Mon, 16-06-2014 03:03:03 -0300"
-/
#guard_msgs in
#eval Formats.rfc850.format date₂
