import Std.Time
open Std.Time

def ISO8601UTC : GenericFormat .any := datespec("uuuu-MM-dd'T'HH:mm:ss.SSSSSSSSSXXX")
def RFC1123 : GenericFormat .any := datespec("eee, dd MMM uuuu HH:mm:ss ZZZ")
def ShortDate : GenericFormat .any := datespec("MM/dd/uuuu")
def LongDate : GenericFormat .any := datespec("MMMM D, uuuu")
def ShortDateTime : GenericFormat .any := datespec("MM/dd/uuuu HH:mm:ss")
def LongDateTime : GenericFormat .any := datespec("MMMM dd, uuuu hh:mm aa")
def Time24Hour : GenericFormat .any := datespec("HH:mm:ss")
def Time12Hour : GenericFormat .any := datespec("hh:mm:ss aa")
def FullDayTimeZone : GenericFormat .any := datespec("EEEE, MMMM dd, uuuu HH:mm:ss ZZZ")
def CustomDayTime : GenericFormat .any := datespec("EEE dd MMM uuuu HH:mm")

def Full12HourWrong : GenericFormat .any := datespec("MM/dd/uuuu hh:mm:ss aa XXX")

-- Dates

def brTZ : TimeZone := timezone("America/Sao_Paulo -03:00")
def jpTZ : TimeZone := timezone("Asia/Tokyo +09:00")

def date₁ := zoned("2014-06-16T03:03:03-03:00")

def time₁ := time("14:11:01")
def time₂ := time("03:11:01")

/--
info: "2014-06-16T03:03:03.000000100-03:00"
-/
#guard_msgs in
#eval
    let t : DateTime := ISO8601UTC.parse! "2014-06-16T03:03:03.000000100-03:00"
    ISO8601UTC.format t

def tm := date₁.toTimestamp
def date₂ := DateTime.ofTimestampWithZone tm brTZ

/--
info: "2014-06-16T03:03:03.000000000-03:00"
-/
#guard_msgs in
#eval
    let t : DateTime := RFC1123.parse! "Mon, 16 Jun 2014 03:03:03 -0300"
    ISO8601UTC.format t

def tm₃ := date₁.toTimestamp
def date₃ := DateTime.ofTimestampWithZone tm₃ brTZ

/--
info: "2014-06-16T00:00:00.000000000Z"
-/
#guard_msgs in
#eval
    let t : DateTime := ShortDate.parse! "06/16/2014"
    ISO8601UTC.format t

-- the timestamp is always related to UTC.

/--
Timestamp: 1723739292
GMT: Thursday, 15 August 2024 16:28:12
BR: 15 August 2024 13:28:12 GMT-03:00
-/
def tm₄ : Second.Offset := 1723739292

def dateBR := DateTime.ofTimestampWithZone (Timestamp.ofSecondsSinceUnixEpoch tm₄) brTZ
def dateJP := DateTime.ofTimestampWithZone (Timestamp.ofSecondsSinceUnixEpoch tm₄) jpTZ
def dateUTC := DateTime.ofTimestampWithZone (Timestamp.ofSecondsSinceUnixEpoch tm₄) .UTC

/--
info: "2024-08-15T13:28:12.000000000-03:00"
-/
#guard_msgs in
#eval
    let t := FullDayTimeZone.parse! "Thursday, August 15, 2024 13:28:12 -0300"
    ISO8601UTC.format t

/--
info: "2024-08-16T01:28:00.000000000Z"
-/
#guard_msgs in
#eval
    let t : DateTime := LongDateTime.parse! "August 16, 2024 01:28 AM"
    ISO8601UTC.format t

/--
info: "0000-12-31T22:28:12.000000000+09:00"
-/
#guard_msgs in
#eval
    let t : DateTime := Time24Hour.parse! "13:28:12"
    ISO8601UTC.format (t.convertZoneRules (TimeZone.ZoneRules.ofTimeZone jpTZ))

/--
info: "0000-12-31T00:00:00.000000000-03:00"
-/
#guard_msgs in
#eval
    let t1 : DateTime := Time12Hour.parse! "03:00:00 AM"
    ISO8601UTC.format (t1.convertZoneRules (TimeZone.ZoneRules.ofTimeZone brTZ))

/--
info: "Thu 15 Aug 2024 16:28"
-/
#guard_msgs in
#eval
    let t2 : DateTime := FullDayTimeZone.parse! "Thursday, August 15, 2024 16:28:12 -0000"
    CustomDayTime.format t2

/--
info: "2024-08-16T13:28:00.000000000Z"
-/
#guard_msgs in
#eval
    let t5 : DateTime := CustomDayTime.parse! "Thu 16 Aug 2024 13:28"
    ISO8601UTC.format t5

/--
info: "2024-08-16T01:28:12.000000000+09:00"
-/
#guard_msgs in
#eval
    let t6 : DateTime := FullDayTimeZone.parse! "Friday, August 16, 2024 01:28:12 +0900"
    ISO8601UTC.format (t6.convertZoneRules (TimeZone.ZoneRules.ofTimeZone jpTZ))

/--
info: "2024-08-16T01:28:12.000000000+09:00"
-/
#guard_msgs in
#eval
    let t7 : DateTime := FullDayTimeZone.parse! "Friday, August 16, 2024 01:28:12 +0900"
    ISO8601UTC.format (t7.convertZoneRules (TimeZone.ZoneRules.ofTimeZone jpTZ))

/--
TM: 1723730627
GMT: Thursday, 15 August 2024 14:03:47
Your time zone: 15 August 2024 11:03:47 GMT-03:00
-/
def localTm : Second.Offset := 1723730627

/--
This PlainDate is relative to the local time.
-/
def PlainDate : PlainDateTime := PlainDateTime.ofWallTime (WallTime.ofSeconds localTm)

def dateBR₁ := DateTime.ofPlainDateTimeWithZone PlainDate brTZ
def dateJP₁ := DateTime.ofPlainDateTimeWithZone PlainDate jpTZ
def dateUTC₁ := DateTime.ofPlainDateTimeWithZone PlainDate .UTC

/--
info: "2024-08-15T14:03:47.000000000-03:00"
-/
#guard_msgs in
#eval
    let t : DateTime := FullDayTimeZone.parse! "Thursday, August 15, 2024 14:03:47 -0300"
    ISO8601UTC.format t

/--
info: "2024-08-15T14:03:47.000000000+09:00"
-/
#guard_msgs in
#eval
    let t1 : DateTime := FullDayTimeZone.parse! "Thursday, August 15, 2024 14:03:47 +0900"
    ISO8601UTC.format t1

/--
info: "2014-06-16T03:03:03.000000000-03:00"
-/
#guard_msgs in
#eval
    let t2 : DateTime := FullDayTimeZone.parse! "Monday, June 16, 2014 03:03:03 -0300"
    ISO8601UTC.format t2

/--
info: Except.ok "1993-05-10T10:30:23.000000000+03:00"
-/
#guard_msgs in
#eval
    let t2 := Full12HourWrong.parse "05/10/1993 10:30:23 AM +03:00"
    (ISO8601UTC.format ·) <$> t2

/--
info: Except.ok "1993-05-10T22:30:23.000000000+03:00"
-/
#guard_msgs in
#eval
    let t2 := Full12HourWrong.parse "05/10/1993 10:30:23 PM +03:00"
    (ISO8601UTC.format ·) <$> t2

/--
info: Except.error "offset 13: need a natural number in the interval of 1 to 12"
-/
#guard_msgs in
#eval
    let t2 := Full12HourWrong.parse "05/10/1993 20:30:23 AM +03:00"
    (ISO8601UTC.format ·) <$> t2

/--
info: Except.error "offset 13: need a natural number in the interval of 1 to 12"
-/
#guard_msgs in
#eval
    let t2 := Full12HourWrong.parse "05/10/1993 20:30:23 PM +03:00"
    (ISO8601UTC.format ·) <$> t2
