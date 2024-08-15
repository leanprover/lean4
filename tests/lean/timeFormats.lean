import Std.Time
open Std.Time

def ISO8601UTC : Format .any := date-spec% "YYYY-MM-DD'T'hh:mm:ssZZZ"
def RFC1123 : Format .any := date-spec% "EEE, DD MMM YYYY hh:mm:ss ZZZ"
def ShortDate : Format .any := date-spec% "MM/DD/YYYY"
def LongDate : Format .any := date-spec% "MMMM D, YYYY"
def ShortDateTime : Format .any := date-spec% "MM/DD/YYYY hh:mm:ss"
def LongDateTime : Format .any := date-spec% "MMMM D, YYYY h:mm aa"
def Time24Hour : Format .any := date-spec% "hh:mm:ss"
def Time12Hour : Format .any := date-spec% "HH:mm:ss aa"
def FullDayTimeZone : Format .any := date-spec% "EEEE, MMMM D, YYYY hh:mm:ss ZZZZ"
def CustomDayTime : Format .any := date-spec% "EEE D MMM YYYY hh:mm"

-- Dates

def brTZ : TimeZone := timezone% "America/Sao_Paulo" -03:00
def jpTZ : TimeZone := timezone% "Asia/Tokyo" +09:00

def date₁ := date% 16-06-2014:03:03:03(brTZ)
def time₁ := time% 14:11:01
def time₂ := time% 03:11:01

/--
info: "Monday, June 16, 2014 03:03:03 -0300"
-/
#guard_msgs in
#eval FullDayTimeZone.format date₁

def tm := date₁.timestamp
def date₂ := DateTime.ofUTCTimestamp tm brTZ

/--
info: "Monday, June 16, 2014 03:03:03 -0300"
-/
#guard_msgs in
#eval FullDayTimeZone.format date₂

def tm₃ := date₁.toTimestamp
def date₃ := DateTime.ofUTCTimestamp tm₃ brTZ

/--
info: "Monday, June 16, 2014 03:03:03 -0300"
-/
#guard_msgs in
#eval FullDayTimeZone.format date₃

-- Section for testing timezone conversion.

-- the timestamp is always related to UTC.

/--
Timestamp: 1723739292
GMT: Thursday, 15 August 2024 16:28:12
BR: 15 August 2024 13:28:12 GMT-03:00
-/
def tm₄ : Second.Offset := 1723739292

def dateBR := DateTime.ofUTCTimestamp (Timestamp.ofSeconds tm₄) brTZ
def dateJP := DateTime.ofUTCTimestamp (Timestamp.ofSeconds tm₄) jpTZ
def dateUTC := DateTime.ofUTCTimestamp (Timestamp.ofSeconds tm₄) .UTC

/--
info: "Thursday, August 15, 2024 13:28:12 -0300"
-/
#guard_msgs in
#eval FullDayTimeZone.format dateBR

/--
info: "Friday, August 16, 2024 01:28:12 +0900"
-/
#guard_msgs in
#eval FullDayTimeZone.format dateJP

/--
info: "Thursday, August 15, 2024 13:28:12 -0300"
-/
#guard_msgs in
#eval FullDayTimeZone.format (dateUTC.convertTimeZone brTZ)

/--
info: "Thursday, August 15, 2024 13:28:12 -0300"
-/
#guard_msgs in
#eval FullDayTimeZone.format (dateJP.convertTimeZone brTZ)

/--
info: "Thursday, August 15, 2024 16:28:12 -0000"
-/
#guard_msgs in
#eval FullDayTimeZone.format dateUTC

/--
info: "Thursday, August 15, 2024 16:28:12 -0000"
-/
#guard_msgs in
#eval FullDayTimeZone.format (dateBR.convertTimeZone .UTC)

/--
info: "Thursday, August 15, 2024 16:28:12 -0000"
-/
#guard_msgs in
#eval FullDayTimeZone.format (dateJP.convertTimeZone .UTC)

/--
info: "Friday, August 16, 2024 01:28:12 +0900"
-/
#guard_msgs in
#eval FullDayTimeZone.format dateJP

/--
info: "Friday, August 16, 2024 01:28:12 +0900"
-/
#guard_msgs in
#eval FullDayTimeZone.format (dateBR.convertTimeZone jpTZ)

/--
info: "Friday, August 16, 2024 01:28:12 +0900"
-/
#guard_msgs in
#eval FullDayTimeZone.format (dateUTC.convertTimeZone jpTZ)

/--
TM: 1723730627
GMT: Thursday, 15 August 2024 14:03:47
Your time zone: 15 Aguust 2024 11:03:47 GMT-03:00
-/
def localTm : Second.Offset := 1723730627

/--
This localDate is relative to the local time.
-/
def localDate : LocalDateTime := Timestamp.toLocalDateTime (Timestamp.ofSeconds localTm)

/--
info: "08/15/2024 14:03:47"
-/
#guard_msgs in
#eval ShortDateTime.formatBuilder localDate.month localDate.day localDate.year localDate.time.hour localDate.minute localDate.time.second

def dateBR₁ := DateTime.ofLocalDateTime localDate brTZ
def dateJP₁ := DateTime.ofLocalDateTime localDate jpTZ
def dateUTC₁ := DateTime.ofLocalDateTime localDate .UTC

/--
info: "Thursday, August 15, 2024 14:03:47 -0300"
-/
#guard_msgs in
#eval FullDayTimeZone.format dateBR₁

/--
info: "Thursday, August 15, 2024 14:03:47 +0900"
-/
#guard_msgs in
#eval FullDayTimeZone.format dateJP₁

/--
info: "Thursday, August 15, 2024 23:03:47 +0900"
-/
#guard_msgs in
#eval FullDayTimeZone.format (dateUTC₁.convertTimeZone jpTZ)

/--
info: "Friday, August 16, 2024 02:03:47 +0900"
-/
#guard_msgs in
#eval FullDayTimeZone.format (dateBR₁.convertTimeZone jpTZ)

/--
info: "Thursday, August 15, 2024 14:03:47 +0900"
-/
#guard_msgs in
#eval FullDayTimeZone.format (dateJP₁.convertTimeZone jpTZ)

/--
info: "Monday, June 16, 2014 03:03:03 -0300"
-/
#guard_msgs in
#eval FullDayTimeZone.format date₂

/--
info: "14:11:01"
-/
#guard_msgs in
#eval Time24Hour.formatBuilder time₁.hour time₁.minute time₁.second

/--
info: "02:11:01 pm"
-/
#guard_msgs in
#eval Time12Hour.formatBuilder time₁.hour time₁.minute time₁.second (if time₁.hour.snd.val > 12 then HourMarker.pm else HourMarker.am)

/--
info: "03:11:01 am"
-/
#guard_msgs in
#eval Time12Hour.formatBuilder time₂.hour time₂.minute time₂.second (if time₂.hour.snd.val > 12 then HourMarker.pm else HourMarker.am)

/--
info: "06/16/2014"
-/
#guard_msgs in
#eval ShortDate.formatBuilder date₁.month date₁.day date₁.year
