import Std.Time
open Std.Time

def ISO8601UTC : GenericFormat .any := datespec("uuuu-MM-dd'T'HH:mm:ss.SSSSSSSSSZ")
def RFC1123 : GenericFormat .any := datespec("eee, dd MMM uuuu HH:mm:ss ZZZ")
def ShortDate : GenericFormat .any := datespec("MM/dd/uuuu")
def LongDate : GenericFormat .any := datespec("MMMM D, uuuu")
def ShortDateTime : GenericFormat .any := datespec("MM/dd/uuuu HH:mm:ss")
def LongDateTime : GenericFormat .any := datespec("MMMM D, uuuu h:mm aa")
def Time24Hour : GenericFormat .any := datespec("HH:mm:ss")
def Time12Hour : GenericFormat .any := datespec("hh:mm:ss aa")
def FullDayTimeZone : GenericFormat .any := datespec("EEEE, MMMM dd, uuuu HH:mm:ss ZZZ")
def CustomDayTime : GenericFormat .any := datespec("EEE dd MMM uuuu HH:mm")
def EraDate : GenericFormat .any := datespec("MM D, uuuu G")

-- Dates

def brTZ : TimeZone := timezone("America/Sao_Paulo -03:00")
def jpTZ : TimeZone := timezone("Asia/Tokyo +09:00")

def date₁ := zoned("2014-06-16T03:03:03-03:00")

def time₁ := time("14:11:01")
def time₂ := time("03:11:01")

/--
info: "Monday, June 16, 2014 03:03:03 -0300"
-/
#guard_msgs in
#eval FullDayTimeZone.format date₁.toDateTime

def tm := date₁.toTimestamp
def date₂ := DateTime.ofTimestamp tm brTZ

/--
info: "Monday, June 16, 2014 03:03:03 -0300"
-/
#guard_msgs in
#eval FullDayTimeZone.format date₂

def tm₃ := date₁.toTimestamp
def date₃ := DateTime.ofTimestamp tm₃ brTZ

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

def dateBR := DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch tm₄) brTZ
def dateJP := DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch tm₄) jpTZ
def dateUTC := DateTime.ofTimestamp (Timestamp.ofSecondsSinceUnixEpoch tm₄) .UTC

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
info: "Thursday, August 15, 2024 16:28:12 +0000"
-/
#guard_msgs in
#eval FullDayTimeZone.format dateUTC

/--
info: "Thursday, August 15, 2024 16:28:12 +0000"
-/
#guard_msgs in
#eval FullDayTimeZone.format (dateBR.convertTimeZone .UTC)

/--
info: "Thursday, August 15, 2024 16:28:12 +0000"
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
Your time zone: 15 August 2024 11:03:47 GMT-03:00
-/
def localTm : Second.Offset := 1723730627

/--
This PlainDate is relative to the local time.
-/
def PlainDate : PlainDateTime := Timestamp.toPlainDateTimeAssumingUTC (Timestamp.ofSecondsSinceUnixEpoch localTm)

def dateBR₁ := DateTime.ofPlainDateTime PlainDate brTZ
def dateJP₁ := DateTime.ofPlainDateTime PlainDate jpTZ
def dateUTC₁ := DateTime.ofPlainDateTime PlainDate .UTC

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

def l := Time12Hour.formatBuilder time₁.hour.toRelative time₁.minute time₁.second (if time₁.hour.val > 12 then HourMarker.pm else HourMarker.am)

/--
info: "02:11:01 PM"
-/
#guard_msgs in
#eval l
/--
info: "03:11:01 AM"
-/
#guard_msgs in
#eval Time12Hour.formatBuilder time₂.hour.toRelative time₂.minute time₂.second (if time₂.hour.val > 12 then HourMarker.pm else HourMarker.am)

/--
info: "06/16/2014"
-/
#guard_msgs in
#eval ShortDate.formatBuilder date₁.month date₁.day date₁.year

/--
info: "0053-06-19"
-/
#guard_msgs in
#eval Formats.sqlDate.format (DateTime.ofPlainDate (PlainDate.ofDaysSinceUNIXEpoch ⟨-700000⟩) .UTC)

/--
info: "-0002-09-16"
-/
#guard_msgs in
#eval Formats.sqlDate.format (DateTime.ofPlainDate (PlainDate.ofDaysSinceUNIXEpoch ⟨-720000⟩) .UTC)

/--
info: "-0084-07-28"
-/
#guard_msgs in
#eval Formats.sqlDate.format (DateTime.ofPlainDate (PlainDate.ofDaysSinceUNIXEpoch ⟨-750000⟩) .UTC)

/--
info: "-0221-09-04"
-/
#guard_msgs in
#eval Formats.sqlDate.format (DateTime.ofPlainDate (PlainDate.ofDaysSinceUNIXEpoch ⟨-800000⟩) .UTC)

/--
info: date("-0221-09-04")
-/
#guard_msgs in
#eval PlainDate.ofDaysSinceUNIXEpoch ⟨-800000⟩

/--
info: date("-0221-09-04")
-/
#guard_msgs in
#eval PlainDate.ofDaysSinceUNIXEpoch ⟨-800000⟩

/--
info: date("2002-07-14")
-/
#guard_msgs in
#eval date("2002-07-14")

/--
info: time("14:13:12.000000000")
-/
#guard_msgs in
#eval time("14:13:12")

/--
info: zoned("2002-07-14T14:13:12.000000000Z")
-/
#guard_msgs in
#eval zoned("2002-07-14T14:13:12Z")

/--
info: zoned("2002-07-14T14:13:12.000000000+09:00")
-/
#guard_msgs in
#eval zoned("2002-07-14T14:13:12+09:00")

/--
info: "2002-07-14"
-/
#guard_msgs in
#eval zoned("2002-07-14T14:13:12+09:00").format "uuuu-MM-dd"

/--
info: "14-13-12"
-/
#guard_msgs in
#eval zoned("2002-07-14T14:13:12+09:00").format "HH-mm-ss"

/-
Format
-/

def time₄ := time("23:13:12.324354679")
def date₄ := date("2002-07-14")
def datetime₅ := PlainDateTime.mk (PlainDate.ofYearMonthDayClip (-2000) 3 4) (PlainTime.mk 12 23 12 0)
def datetime₄ := datetime("2002-07-14T23:13:12.324354679")
def zoned₄ := zoned("2002-07-14T23:13:12.324354679+09:00")
def zoned₅ := zoned("2002-07-14T23:13:12.324354679+00:00")
def tz : TimeZone := { offset := { second := -3600 }, name := "America/Sao_Paulo", abbreviation := "BRT", isDST := false}
def zoned₆ := ZonedDateTime.ofPlainDateTime (zoned₄.toPlainDateTime) (TimeZone.ZoneRules.ofTimeZone tz)

/--
info: "CE CE CE Common Era C"
-/
#guard_msgs in
#eval zoned₄.format "G GG GGG GGGG GGGGG"

/--
info: "02 2002 000002002"
-/
#guard_msgs in
#eval zoned₄.format "yy yyyy yyyyyyyyy"

/--
info: "02 2002 000002002"
-/
#guard_msgs in
#eval zoned₄.format "uu uuuu uuuuuuuuu"

/--
info: "195 195 195"
-/
#guard_msgs in
#eval zoned₄.format "D DD DDD"

/--
info: "14 14 014 0014 00014"
-/
#guard_msgs in
#eval zoned₄.format "d dd ddd dddd ddddd"

/--
info: "7 07 Jul July J"
-/
#guard_msgs in
#eval zoned₄.format "M MM MMM MMMM MMMMM"

/--
info: "3 03 3rd quarter 3"
-/
#guard_msgs in
#eval zoned₄.format "Q QQ QQQQ QQQQQ"

/--
info: "28 28 028 0028"
-/
#guard_msgs in
#eval zoned₄.format "w ww www wwww"

/--
info: "2 02 002 0002"
-/
#guard_msgs in
#eval zoned₄.format "W WW WWW WWWW"

/--
info: "Sun Sun Sun Sunday S"
-/
#guard_msgs in
#eval zoned₄.format "E EE EEE EEEE EEEEE"

/--
info: "7 07 Sun Sunday S"
-/
#guard_msgs in
#eval zoned₄.format "e ee eee eeee eeeee"

/--
info: "2 02 002 0002"
-/
#guard_msgs in
#eval zoned₄.format "F FF FFF FFFF"

/--
info: "11 11 011 0011 0011"
-/
#guard_msgs in
#eval zoned₄.format "h hh hhh hhhh hhhh"

/--
info: "11 11 011 0011 000011"
-/
#guard_msgs in
#eval zoned₄.format "K KK KKK KKKK KKKKKK"

/--
info: "23 23 023 0023 000023"
-/
#guard_msgs in
#eval zoned₄.format "k kk kkk kkkk kkkkkk"

/--
info: "23 23 023 0023 00023"
-/
#guard_msgs in
#eval zoned₄.format "H HH HHH HHHH HHHHH"

/--
info: "13 13 013 0013 00013"
-/
#guard_msgs in
#eval zoned₄.format "m mm mmm mmmm mmmmm"

/--
info: "12 12 012 0012 00012"
-/
#guard_msgs in
#eval zoned₄.format "s ss sss ssss sssss"


/--
info: "3 32 324 3243 32435"
-/#guard_msgs in
#eval zoned₄.format "S SS SSS SSSS SSSSS"

/--
info: "83592324 83592324 83592324 83592324 083592324"
-/
#guard_msgs in
#eval zoned₄.format "A AA AAA AAAA AAAAAAAAA"

/--
info: "324354679 324354679 324354679 324354679 324354679"
-/
#guard_msgs in
#eval zoned₄.format "n nn nnn nnnn nnnnnnnnn"

/--
info: "83592324354679 83592324354679 83592324354679 83592324354679 83592324354679"
-/
#guard_msgs in
#eval zoned₄.format "N NN NNN NNNN NNNNNNNNN"

/--
info: "+09:00"
-/
#guard_msgs in
#eval zoned₄.format "VV"

/--
info: "+09:00 +09:00 +09:00 +09:00"
-/
#guard_msgs in
#eval zoned₄.format "z zz zzzz zzzz"

/--
info: "+00:00 +00:00 +00:00 +00:00"
-/
#guard_msgs in
#eval zoned₅.format "z zz zzzz zzzz"

/--
info: "GMT+9 GMT+09:00"
-/
#guard_msgs in
#eval zoned₄.format "O OOOO"

/--
info: "+09 +0900 +09:00 +0900 +09:00"
-/
#guard_msgs in
#eval zoned₄.format "X XX XXX XXXX XXXXX"

/--
info: "+09 +0900 +09:00 +0900 +09:00"
-/
#guard_msgs in
#eval zoned₄.format "x xx xxx xxxx xxxxx"

/--
info: "Z Z Z Z Z"
-/
#guard_msgs in
#eval zoned₅.format "X XX XXX XXXX XXXXX"

/--
info: "+00 +0000 +00:00 +0000 +00:00"
-/
#guard_msgs in
#eval zoned₅.format "x xx xxx xxxx xxxxx"

/--
info: "+0900 +0900 +0900 GMT+09:00 +09:00"
-/
#guard_msgs in
#eval zoned₄.format "Z ZZ ZZZ ZZZZ ZZZZZ"

/--
info: "CE CE CE Common Era C"
-/
#guard_msgs in
#eval datetime₄.format "G GG GGG GGGG GGGGG"

/--
info: "02 2002 000002002"
-/
#guard_msgs in
#eval datetime₄.format "yy yyyy yyyyyyyyy"

/--
info: "02 2002 000002002"
-/
#guard_msgs in
#eval datetime₄.format "uu uuuu uuuuuuuuu"

/--
info: "195 195 195"
-/
#guard_msgs in
#eval datetime₄.format "D DD DDD"

/--
info: "7 07 Jul J"
-/
#guard_msgs in
#eval datetime₄.format "M MM MMM MMMMM"

/--
info: "14 14 014 0014 00014"
-/
#guard_msgs in
#eval datetime₄.format "d dd ddd dddd ddddd"

/--
info: "7 07 Jul July J"
-/
#guard_msgs in
#eval datetime₄.format "M MM MMM MMMM MMMMM"

/--
info: "14 14 0014 0014"
-/#guard_msgs in
#eval datetime₄.format "d dd dddd dddd"

/--
info: "3 03 3rd quarter 3"
-/
#guard_msgs in
#eval datetime₄.format "Q QQ QQQQ QQQQQ"

/--
info: "28 28 028 0028"
-/
#guard_msgs in
#eval datetime₄.format "w ww www wwww"

/--
info: "2 02 002 0002"
-/
#guard_msgs in
#eval datetime₄.format "W WW WWW WWWW"

/--
info: "Sun Sun Sun Sunday S"
-/
#guard_msgs in
#eval datetime₄.format "E EE EEE EEEE EEEEE"

/--
info: "7 07 Sun Sunday S"
-/
#guard_msgs in
#eval datetime₄.format "e ee eee eeee eeeee"

/--
info: "2 02 002 0002"
-/
#guard_msgs in
#eval datetime₄.format "F FF FFF FFFF"

/--
info: "11 11 011 0011 0011"
-/
#guard_msgs in
#eval datetime₄.format "h hh hhh hhhh hhhh"

/--
info: "11 11 011 0011 000011"
-/
#guard_msgs in
#eval datetime₄.format "K KK KKK KKKK KKKKKK"

/--
info: "23 23 023 0023 000023"
-/
#guard_msgs in
#eval datetime₄.format "k kk kkk kkkk kkkkkk"

/--
info: "23 23 023 0023 00023"
-/
#guard_msgs in
#eval datetime₄.format "H HH HHH HHHH HHHHH"

/--
info: "13 13 013 0013 00013"
-/
#guard_msgs in
#eval datetime₄.format "m mm mmm mmmm mmmmm"

/--
info: "12 12 012 0012 00012"
-/
#guard_msgs in
#eval datetime₄.format "s ss sss ssss sssss"


/--
info: "3 32 324 3243 32435"
-/#guard_msgs in
#eval datetime₄.format "S SS SSS SSSS SSSSS"

/--
info: "3 32 324 3243 324354679"
-/
#guard_msgs in
#eval datetime₄.format "S SS SSS SSSS SSSSSSSSS"

/--
info: "83592324 83592324 83592324 83592324 083592324"
-/
#guard_msgs in
#eval datetime₄.format "A AA AAA AAAA AAAAAAAAA"

/--
info: "324354679 324354679 324354679 324354679 324354679"
-/
#guard_msgs in
#eval datetime₄.format "n nn nnn nnnn nnnnnnnnn"

/--
info: "83592324354679 83592324354679 83592324354679 83592324354679 83592324354679"
-/
#guard_msgs in
#eval datetime₄.format "N NN NNN NNNN NNNNNNNNN"

/--
info: "11 11 011 0011 0011"
-/
#guard_msgs in
#eval time₄.format "h hh hhh hhhh hhhh"

/--
info: "11 11 011 0011 000011"
-/
#guard_msgs in
#eval time₄.format "K KK KKK KKKK KKKKKK"

/--
info: "23 23 023 0023 000023"

-/
#guard_msgs in
#eval time₄.format "k kk kkk kkkk kkkkkk"

/--
info: "23 23 023 0023 00023"
-/
#guard_msgs in
#eval time₄.format "H HH HHH HHHH HHHHH"

/--
info: "13 13 013 0013 00013"
-/
#guard_msgs in
#eval time₄.format "m mm mmm mmmm mmmmm"

/--
info: "12 12 012 0012 00012"
-/
#guard_msgs in
#eval time₄.format "s ss sss ssss sssss"


/--
info: "3 32 324 3243 32435"
-/#guard_msgs in
#eval time₄.format "S SS SSS SSSS SSSSS"

/--
info: "3 32 324 3243 324354679"
-/
#guard_msgs in
#eval time₄.format "S SS SSS SSSS SSSSSSSSS"

/--
info: "83592324 83592324 83592324 83592324 083592324"
-/
#guard_msgs in
#eval time₄.format "A AA AAA AAAA AAAAAAAAA"

/--
info: "324354679 324354679 324354679 324354679 324354679"
-/
#guard_msgs in
#eval time₄.format "n nn nnn nnnn nnnnnnnnn"

/--
info: "83592324354679 83592324354679 83592324354679 83592324354679 83592324354679"
-/
#guard_msgs in
#eval time₄.format "N NN NNN NNNN NNNNNNNNN"

/--
info: "CE CE CE Common Era C"
-/
#guard_msgs in
#eval date₄.format "G GG GGG GGGG GGGGG"

/--
info: "02 2002 000002002"
-/
#guard_msgs in
#eval date₄.format "yy yyyy yyyyyyyyy"

/--
info: "02 2002 000002002"
-/
#guard_msgs in
#eval date₄.format "uu uuuu uuuuuuuuu"

/--
info: "195 195 195"
-/
#guard_msgs in
#eval date₄.format "D DD DDD"

/--
info: "7 07 Jul J"
-/
#guard_msgs in
#eval date₄.format "M MM MMM MMMMM"

/--
info: "14 14 014 0014 00014"
-/
#guard_msgs in
#eval date₄.format "d dd ddd dddd ddddd"

/--
info: "7 07 Jul July J"
-/
#guard_msgs in
#eval date₄.format "M MM MMM MMMM MMMMM"

/--
info: "14 14 0014 0014"
-/#guard_msgs in
#eval date₄.format "d dd dddd dddd"

/--
info: "3 03 3rd quarter 3"
-/
#guard_msgs in
#eval date₄.format "Q QQ QQQQ QQQQQ"

/--
info: "28 28 028 0028"
-/
#guard_msgs in
#eval date₄.format "w ww www wwww"

/--
info: "2 02 002 0002"
-/
#guard_msgs in
#eval date₄.format "W WW WWW WWWW"

/--
info: "Sun Sun Sun Sunday S"
-/
#guard_msgs in
#eval date₄.format "E EE EEE EEEE EEEEE"

/--
info: "7 07 Sun Sunday S"
-/
#guard_msgs in
#eval date₄.format "e ee eee eeee eeeee"

/--
info: "2 02 002 0002"
-/
#guard_msgs in
#eval date₄.format "F FF FFF FFFF"

/--
info: "-2000 2001 BCE"
-/
#guard_msgs in
#eval datetime₅.format "uuuu yyyy G"

/--
info: "2002 2002 CE"
-/
#guard_msgs in
#eval datetime₄.format "uuuu yyyy G"

/--
info: "BRT BRT BRT America/Sao_Paulo America/Sao_Paulo"
-/
#guard_msgs in
#eval zoned₆.format "z zz zzz zzzz zzzz"

/--
info: 1
-/
#guard_msgs in
#eval
  let t : ZonedDateTime := .ofPlainDateTime datetime("2018-12-31T12:00:00") (TimeZone.ZoneRules.ofTimeZone TimeZone.UTC)
  IO.println s!"{t.format "w"}"

/-
Truncation Test
-/

/--
info: ("19343232432-01-04T01:04:03.000000000",
 Except.ok (datetime("19343232432-01-04T01:04:03.000000000")),
 datetime("1932-01-02T05:04:03.000000000"))
-/
#guard_msgs in
#eval
  let r := PlainDateTime.mk (PlainDate.ofYearMonthDayClip 19343232432 1 4) (PlainTime.mk 25 64 3 0)
  let s := r.toLeanDateTimeString
  let r := PlainDateTime.parse s
  (s, r, datetime("1932-01-02T05:04:03.000000000"))
