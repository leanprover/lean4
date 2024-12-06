import Std.Time
import Init
open Std.Time

/-
Test for quantity
-/

#eval do
  let res ← Database.defaultGetZoneRules "America/Sao_Paulo"
  if res.transitions.size < 1 then
    throw <| IO.userError "invalid quantity for America/Sao_Paulo"

/--
info: { second := 0 }
-/
#guard_msgs in
#eval do
  let res ← Database.defaultGetZoneRules "UTC"
  println! repr res.initialLocalTimeType.gmtOffset

/-
The idea is just to check if there's no errors while computing the local zone rules.
-/
#eval do
  discard <| Database.defaultGetLocalZoneRules

/-
Java:
2013-10-19T23:59:59-03:00[America/Sao_Paulo] 1382237999
2013-10-20T01:00-02:00[America/Sao_Paulo] 1382238000
2013-10-20T01:00:01-02:00[America/Sao_Paulo] 1382238001
-/

/--
info: 2013-10-19T23:59:59.000000000-03:00
2013-10-20T00:00:00.000000000-02:00
2013-10-20T00:00:01.000000000-02:00
-/
#guard_msgs in
#eval do
  let zr ← Database.defaultGetZoneRules "America/Sao_Paulo"
  println! "{ZonedDateTime.ofPlainDateTime datetime("2013-10-19T23:59:59") zr |>.toLeanDateTimeWithZoneString}"
  println! "{ZonedDateTime.ofPlainDateTime datetime("2013-10-20T00:00:00") zr |>.toLeanDateTimeWithZoneString}"
  println! "{ZonedDateTime.ofPlainDateTime datetime("2013-10-20T00:00:01") zr |>.toLeanDateTimeWithZoneString}"

/-
Java:
2019-11-03T01:59:59-05:00[America/Chicago] 1572764399
2019-11-03T02:00-06:00[America/Chicago] 1572768000
2019-11-03T02:59:59-06:00[America/Chicago] 1572771599
-/

/--
info: 2019-11-03T01:59:59.000000000-05:00
2019-11-03T02:00:00.000000000-06:00
2019-11-03T02:59:59.000000000-06:00
-/
#guard_msgs in
#eval do
  let zr ← Database.defaultGetZoneRules "America/Chicago"
  println! "{ZonedDateTime.ofPlainDateTime datetime("2019-11-03T01:59:59") zr |>.toLeanDateTimeWithZoneString}"
  println! "{ZonedDateTime.ofPlainDateTime datetime("2019-11-03T02:00:00") zr |>.toLeanDateTimeWithZoneString}"
  println! "{ZonedDateTime.ofPlainDateTime datetime("2019-11-03T02:59:59") zr |>.toLeanDateTimeWithZoneString}"

/-
Java:
2003-10-26T01:59:59-05:00[America/Monterrey] 1067151599
2003-10-26T02:00-06:00[America/Monterrey] 1067155200
2003-10-26T02:59:59-06:00[America/Monterrey] 1067158799
-/

/--
info: 2003-10-26T01:59:59.000000000-05:00
2003-10-26T02:00:00.000000000-06:00
2003-10-26T02:59:59.000000000-06:00
-/
#guard_msgs in
#eval do
  let zr ← Database.defaultGetZoneRules "America/Monterrey"
  println! "{ZonedDateTime.ofPlainDateTime datetime("2003-10-26T01:59:59") zr |>.toLeanDateTimeWithZoneString}"
  println! "{ZonedDateTime.ofPlainDateTime datetime("2003-10-26T02:00:00") zr |>.toLeanDateTimeWithZoneString}"
  println! "{ZonedDateTime.ofPlainDateTime datetime("2003-10-26T02:59:59") zr |>.toLeanDateTimeWithZoneString}"
