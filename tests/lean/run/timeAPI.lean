import Std.Time
import Init
open Std.Time

def sao_paulo : TimeZone.ZoneRules :=
  {
    initialLocalTimeType :=
      {
        gmtOffset := { second := -11188 },
        isDst := false,
        abbreviation := "LMT",
        wall := Std.Time.TimeZone.StdWall.standard,
        utLocal := Std.Time.TimeZone.UTLocal.ut,
        identifier := "America/Sao_Paulo"
      },
    transitions := #[
      {
        time := 782276400,
        localTimeType := {
          gmtOffset := { second := -7200 },
          isDst := true,
          abbreviation := "-02",
          wall := Std.Time.TimeZone.StdWall.standard,
          utLocal := Std.Time.TimeZone.UTLocal.ut,
          identifier := "America/Sao_Paulo"
        }
      },
      { time := 793159200,
        localTimeType := {
          gmtOffset := { second := -10800 },
          isDst := false,
          abbreviation := "-03",
          wall := Std.Time.TimeZone.StdWall.standard,
          utLocal := Std.Time.TimeZone.UTLocal.ut,
          identifier := "America/Sao_Paulo"
        }
      },
      { time := 813726000,
        localTimeType := {
          gmtOffset := { second := -7200 },
          isDst := true,
          abbreviation := "-02",
          wall := Std.Time.TimeZone.StdWall.standard,
          utLocal := Std.Time.TimeZone.UTLocal.ut,
          identifier := "America/Sao_Paulo"
        }
      },
      { time := 824004000,
        localTimeType := {
          gmtOffset := { second := -10800 },
          isDst := false,
          abbreviation := "-03",
          wall := Std.Time.TimeZone.StdWall.standard,
          utLocal := Std.Time.TimeZone.UTLocal.ut,
          identifier := "America/Sao_Paulo"
        }
      },
      { time := 844570800,
        localTimeType := {
          gmtOffset := { second := -7200 },
          isDst := true,
          abbreviation := "-02",
          wall := Std.Time.TimeZone.StdWall.standard,
          utLocal := Std.Time.TimeZone.UTLocal.ut,
          identifier := "America/Sao_Paulo"
        }
      },
      { time := 856058400,
        localTimeType := {
          gmtOffset := { second := -10800 },
          isDst := false,
          abbreviation := "-03",
          wall := Std.Time.TimeZone.StdWall.standard,
          utLocal := Std.Time.TimeZone.UTLocal.ut,
          identifier := "America/Sao_Paulo"
        }
      },
      { time := 876106800,
        localTimeType := {
          gmtOffset := { second := -7200 },
          isDst := true,
          abbreviation := "-02",
          wall := Std.Time.TimeZone.StdWall.standard,
          utLocal := Std.Time.TimeZone.UTLocal.ut,
          identifier := "America/Sao_Paulo"
        }
      },
      { time := 888717600,
        localTimeType := {
          gmtOffset := { second := -10800 },
          isDst := false,
          abbreviation := "-03",
          wall := Std.Time.TimeZone.StdWall.standard,
          utLocal := Std.Time.TimeZone.UTLocal.ut,
          identifier := "America/Sao_Paulo"
        }
      },
      { time := 908074800,
        localTimeType := {
          gmtOffset := { second := -7200 },
          isDst := true,
          abbreviation := "-02",
          wall := Std.Time.TimeZone.StdWall.standard,
          utLocal := Std.Time.TimeZone.UTLocal.ut,
          identifier := "America/Sao_Paulo"
        }
      },
      { time := 919562400,
        localTimeType := {
          gmtOffset := { second := -10800 },
          isDst := false,
          abbreviation := "-03",
          wall := Std.Time.TimeZone.StdWall.standard,
          utLocal := Std.Time.TimeZone.UTLocal.ut,
          identifier := "America/Sao_Paulo"
        }
      },
      { time := 938919600,
        localTimeType := {
          gmtOffset := { second := -7200 },
          isDst := true,
          abbreviation := "-02",
          wall := Std.Time.TimeZone.StdWall.standard,
          utLocal := Std.Time.TimeZone.UTLocal.ut,
          identifier := "America/Sao_Paulo"
        }
      },
      { time := 951616800,
        localTimeType := {
          gmtOffset := { second := -10800 },
          isDst := false,
          abbreviation := "-03",
          wall := Std.Time.TimeZone.StdWall.standard,
          utLocal := Std.Time.TimeZone.UTLocal.ut,
          identifier := "America/Sao_Paulo"
        }
      },
      { time := 970974000,
        localTimeType := {
          gmtOffset := { second := -7200 },
          isDst := true,
          abbreviation := "-02",
          wall := Std.Time.TimeZone.StdWall.standard,
          utLocal := Std.Time.TimeZone.UTLocal.ut,
          identifier := "America/Sao_Paulo"
        }
      },
      { time := 982461600,
        localTimeType := {
          gmtOffset := { second := -10800 },
          isDst := false,
          abbreviation := "-03",
          wall := Std.Time.TimeZone.StdWall.standard,
          utLocal := Std.Time.TimeZone.UTLocal.ut,
          identifier := "America/Sao_Paulo"
        }
      },
      { time := 1003028400,
        localTimeType := {
          gmtOffset := { second := -7200 },
          isDst := true,
          abbreviation := "-02",
          wall := Std.Time.TimeZone.StdWall.standard,
          utLocal := Std.Time.TimeZone.UTLocal.ut,
          identifier := "America/Sao_Paulo"
        }
      },
      { time := 1013911200,
        localTimeType := {
          gmtOffset := { second := -10800 },
          isDst := false,
          abbreviation := "-03",
          wall := Std.Time.TimeZone.StdWall.standard,
          utLocal := Std.Time.TimeZone.UTLocal.ut,
          identifier := "America/Sao_Paulo"
        }
      },
      { time := 1036292400,
        localTimeType := {
          gmtOffset := { second := -7200 },
          isDst := true,
          abbreviation := "-02",
          wall := Std.Time.TimeZone.StdWall.standard,
          utLocal := Std.Time.TimeZone.UTLocal.ut,
          identifier := "America/Sao_Paulo"
        }
      },
      { time := 1045360800,
        localTimeType := {
          gmtOffset := { second := -10800 },
          isDst := false,
          abbreviation := "-03",
          wall := Std.Time.TimeZone.StdWall.standard,
          utLocal := Std.Time.TimeZone.UTLocal.ut,
          identifier := "America/Sao_Paulo"
        }
      },
      { time := 1066532400,
        localTimeType := {
          gmtOffset := { second := -7200 },
          isDst := true,
          abbreviation := "-02",
          wall := Std.Time.TimeZone.StdWall.standard,
          utLocal := Std.Time.TimeZone.UTLocal.ut,
          identifier := "America/Sao_Paulo"
        }
      }
    ]
  }

/-
Unit conversion tests.
-/

/--
info: --- nanosecond
nanoseconds: 1209600000000000
milliseconds: 1209600000
seconds: 1209600
minutes: 20160
hours: 336
days: 14
weeks: 2
--- millisecond
nanoseconds: 1209600000000000
seconds: 1209600
milliseconds: 1209600000
minutes: 20160
hours: 336
days: 14
weeks: 2
--- second
nanoseconds: 1209600000000000
milliseconds: 1209600000
seconds: 1209600
minutes: 20160
hours: 336
days: 14
weeks: 2
--- minute
nanoseconds: 1209600000000000
milliseconds: 1209600000
seconds: 1209600
minutes: 20160
hours: 336
days: 14
weeks: 2
--- hour
nanoseconds: 1209600000000000
milliseconds: 1209600000
seconds: 1209600
minutes: 20160
hours: 336
days: 14
weeks: 2
--- day
nanoseconds: 1209600000000000
milliseconds: 1209600000
seconds: 1209600
minutes: 20160
hours: 336
days: 14
weeks: 2
--- week
nanoseconds: 1209600000000000
milliseconds: 1209600000
seconds: 1209600
minutes: 20160
hours: 336
days: 14
weeks: 2

-/
#guard_msgs in
#eval do
  let nanosecond: Nanosecond.Offset := 1209600000000000
  println! s!"--- nanosecond"
  println! s!"nanoseconds: {nanosecond}"
  println! s!"milliseconds: {nanosecond.toMilliseconds}"
  println! s!"seconds: {nanosecond.toSeconds}"
  println! s!"minutes: {nanosecond.toMinutes}"
  println! s!"hours: {nanosecond.toHours}"
  println! s!"days: {nanosecond.toDays}"
  println! s!"weeks: {nanosecond.toWeeks}"
  -- Cannot do this for months or years because sizes are variable.

  let millisecond: Millisecond.Offset := 1209600000
  println! s!"--- millisecond"
  println! s!"nanoseconds: {millisecond.toNanoseconds}"
  println! s!"seconds: {millisecond.toSeconds}"
  println! s!"milliseconds: {millisecond}"
  println! s!"minutes: {millisecond.toMinutes}"
  println! s!"hours: {millisecond.toHours}"
  println! s!"days: {millisecond.toDays}"
  println! s!"weeks: {millisecond.toWeeks}"
  -- Cannot do this for months or years because sizes are variable.

  let second : Second.Offset := 1209600
  println! s!"--- second"
  println! s!"nanoseconds: {second.toNanoseconds}"
  println! s!"milliseconds: {second.toMilliseconds}"
  println! s!"seconds: {second}"
  println! s!"minutes: {second.toMinutes}"
  println! s!"hours: {second.toHours}"
  println! s!"days: {second.toDays}"
  println! s!"weeks: {second.toWeeks}"
  -- Cannot do this for months or years because sizes are variable.

  let minute: Minute.Offset := 20160
  println! s!"--- minute"
  println! s!"nanoseconds: {minute.toNanoseconds}"
  println! s!"milliseconds: {minute.toMilliseconds}"
  println! s!"seconds: {minute.toSeconds}"
  println! s!"minutes: {minute}"
  println! s!"hours: {minute.toHours}"
  println! s!"days: {minute.toDays}"
  println! s!"weeks: {minute.toWeeks}"
  -- Cannot do this for months or years because sizes are variable.

  let hour: Hour.Offset := 336
  println! s!"--- hour"
  println! s!"nanoseconds: {hour.toNanoseconds}"
  println! s!"milliseconds: {hour.toMilliseconds}"
  println! s!"seconds: {hour.toSeconds}"
  println! s!"minutes: {hour.toMinutes}"
  println! s!"hours: {hour}"
  println! s!"days: {hour.toDays}"
  println! s!"weeks: {hour.toWeeks}"
  -- Cannot do this for months or years because sizes are variable.

  let day: Day.Offset := 14
  println! s!"--- day"
  println! s!"nanoseconds: {day.toNanoseconds}"
  println! s!"milliseconds: {day.toMilliseconds}"
  println! s!"seconds: {day.toSeconds}"
  println! s!"minutes: {day.toMinutes}"
  println! s!"hours: {day.toHours}"
  println! s!"days: {day}"
  println! s!"weeks: {day.toWeeks}"
  -- Cannot do this for months or years because sizes are variable.

  let week: Week.Offset := 2
  println! s!"--- week"
  println! s!"nanoseconds: {week.toNanoseconds}"
  println! s!"milliseconds: {week.toMilliseconds}"
  println! s!"seconds: {week.toSeconds}"
  println! s!"minutes: {week.toMinutes}"
  println! s!"hours: {week.toHours}"
  println! s!"days: {week.toDays}"
  println! s!"weeks: {week}"
  -- Cannot do this for months or years because sizes are variable.

theorem nano_nano_nano : (1 : Nanosecond.Offset) + (1 : Nanosecond.Offset) = (2 : Nanosecond.Offset) := rfl
theorem nano_milli_nano : (1 : Nanosecond.Offset) + (1 : Millisecond.Offset) = (1000001 : Nanosecond.Offset) := rfl
theorem nano_sec_nano : (1 : Nanosecond.Offset) + (1 : Second.Offset) = (1000000001 : Nanosecond.Offset) := rfl
theorem nano_min_nano : (1 : Nanosecond.Offset) + (1 : Minute.Offset) = (60000000001 : Nanosecond.Offset) := rfl
theorem nano_hour_nano : (1 : Nanosecond.Offset) + (1 : Hour.Offset) = (3600000000001 : Nanosecond.Offset) := rfl
theorem nano_day_nano : (1 : Nanosecond.Offset) + (1 : Day.Offset) = (86400000000001 : Nanosecond.Offset) := rfl
theorem nano_week_nano : (1 : Nanosecond.Offset) + (1 : Week.Offset) = (604800000000001 : Nanosecond.Offset) := rfl

theorem milli_nano_nano : (1 : Millisecond.Offset) + (1 : Nanosecond.Offset) = (1000001 : Nanosecond.Offset) := rfl
theorem milli_milli_milli : (1 : Millisecond.Offset) + (1 : Millisecond.Offset) = (2 : Millisecond.Offset) := rfl
theorem milli_sec_milli : (1 : Millisecond.Offset) + (1 : Second.Offset) = (1001 : Millisecond.Offset) := rfl
theorem milli_min_milli : (1 : Millisecond.Offset) + (1 : Minute.Offset) = (60001 : Millisecond.Offset) := rfl
theorem milli_hour_milli : (1 : Millisecond.Offset) + (1 : Hour.Offset) = (3600001 : Millisecond.Offset) := rfl
theorem milli_day_milli : (1 : Millisecond.Offset) + (1 : Day.Offset) = (86400001 : Millisecond.Offset) := rfl
theorem milli_week_milli : (1 : Millisecond.Offset) + (1 : Week.Offset) = (604800001 : Millisecond.Offset) := rfl

theorem sec_nano_nano : (1 : Second.Offset) + (1 : Nanosecond.Offset) = (1000000001 : Nanosecond.Offset) := rfl
theorem sec_milli_milli : (1 : Second.Offset) + (1 : Millisecond.Offset) = (1001 : Millisecond.Offset) := rfl
theorem sec_sec_sec : (1 : Second.Offset) + (1 : Second.Offset) = (2 : Second.Offset) := rfl
theorem sec_min_sec : (1 : Second.Offset) + (1 : Minute.Offset) = (61 : Second.Offset) := rfl
theorem sec_hour_sec : (1 : Second.Offset) + (1 : Hour.Offset) = (3601 : Second.Offset) := rfl
theorem sec_day_sec : (1 : Second.Offset) + (1 : Day.Offset) = (86401 : Second.Offset) := rfl
theorem sec_week_sec : (1 : Second.Offset) + (1 : Week.Offset) = (604801 : Second.Offset) := rfl

theorem min_nano_nano : (1 : Minute.Offset) + (1 : Nanosecond.Offset) = (60000000001 : Nanosecond.Offset) := rfl
theorem min_milli_milli : (1 : Minute.Offset) + (1 : Millisecond.Offset) = (60001 : Millisecond.Offset) := rfl
theorem min_sec_sec : (1 : Minute.Offset) + (1 : Second.Offset) = (61 : Second.Offset) := rfl
theorem min_min_min : (1 : Minute.Offset) + (1 : Minute.Offset) = (2 : Minute.Offset) := rfl
theorem min_hour_min : (1 : Minute.Offset) + (1 : Hour.Offset) = (61 : Minute.Offset) := rfl
theorem min_day_min : (1 : Minute.Offset) + (1 : Day.Offset) = (1441 : Minute.Offset) := rfl
theorem min_week_min : (1 : Minute.Offset) + (1 : Week.Offset) = (10081 : Minute.Offset) := rfl

theorem hour_nano_nano : (1 : Hour.Offset) + (1 : Nanosecond.Offset) = (3600000000001 : Nanosecond.Offset) := rfl
theorem hour_milli_milli : (1 : Hour.Offset) + (1 : Millisecond.Offset) = (3600001 : Millisecond.Offset) := rfl
theorem hour_sec_sec : (1 : Hour.Offset) + (1 : Second.Offset) = (3601 : Second.Offset) := rfl
theorem hour_min_min : (1 : Hour.Offset) + (1 : Minute.Offset) = (61 : Minute.Offset) := rfl
theorem hour_hour_hour : (1 : Hour.Offset) + (1 : Hour.Offset) = (2 : Hour.Offset) := rfl
theorem hour_day_hour : (1 : Hour.Offset) + (1 : Day.Offset) = (25 : Hour.Offset) := rfl
theorem hour_week_hour : (1 : Hour.Offset) + (1 : Week.Offset) = (169 : Hour.Offset) := rfl

theorem day_nano_nano : (1 : Day.Offset) + (1 : Nanosecond.Offset) = (86400000000001 : Nanosecond.Offset) := rfl
theorem day_milli_milli : (1 : Day.Offset) + (1 : Millisecond.Offset) = (86400001 : Millisecond.Offset) := rfl
theorem day_sec_sec : (1 : Day.Offset) + (1 : Second.Offset) = (86401 : Second.Offset) := rfl
theorem day_min_min : (1 : Day.Offset) + (1 : Minute.Offset) = (1441 : Minute.Offset) := rfl
theorem day_hour_hour : (1 : Day.Offset) + (1 : Hour.Offset) = (25 : Hour.Offset) := rfl
theorem day_day_day : (1 : Day.Offset) + (1 : Day.Offset) = (2 : Day.Offset) := rfl
theorem day_week_day : (1 : Day.Offset) + (1 : Week.Offset) = (8 : Day.Offset) := rfl

theorem week_nano_nano : (1 : Week.Offset) + (1 : Nanosecond.Offset) = (604800000000001 : Nanosecond.Offset) := rfl
theorem week_milli_milli : (1 : Week.Offset) + (1 : Millisecond.Offset) = (604800001 : Millisecond.Offset) := rfl
theorem week_sec_sec : (1 : Week.Offset) + (1 : Second.Offset) = (604801 : Second.Offset) := rfl
theorem week_min_min : (1 : Week.Offset) + (1 : Minute.Offset) = (10081 : Minute.Offset) := rfl
theorem week_hour_hour : (1 : Week.Offset) + (1 : Hour.Offset) = (169 : Hour.Offset) := rfl
theorem week_day_day : (1 : Week.Offset) + (1 : Day.Offset) = (8 : Day.Offset) := rfl
theorem week_week_week : (1 : Week.Offset) + (1 : Week.Offset) = (2 : Week.Offset) := rfl

theorem nano_nano_nano_sub : (1 : Nanosecond.Offset) - (1 : Nanosecond.Offset) = (0 : Nanosecond.Offset) := rfl
theorem nano_milli_nano_sub : (1 : Nanosecond.Offset) - (1 : Millisecond.Offset) = (-999999 : Nanosecond.Offset) := rfl
theorem nano_sec_nano_sub : (1 : Nanosecond.Offset) - (1 : Second.Offset) = (-999999999 : Nanosecond.Offset) := rfl
theorem nano_min_nano_sub : (1 : Nanosecond.Offset) - (1 : Minute.Offset) = (-59999999999 : Nanosecond.Offset) := rfl
theorem nano_hour_nano_sub : (1 : Nanosecond.Offset) - (1 : Hour.Offset) = (-3599999999999 : Nanosecond.Offset) := rfl
theorem nano_day_nano_sub : (1 : Nanosecond.Offset) - (1 : Day.Offset) = (-86399999999999 : Nanosecond.Offset) := rfl
theorem nano_week_nano_sub : (1 : Nanosecond.Offset) - (1 : Week.Offset) = (-604799999999999 : Nanosecond.Offset) := rfl

theorem milli_nano_nano_sub : (1 : Millisecond.Offset) - (1 : Nanosecond.Offset) = (999999 : Nanosecond.Offset) := rfl
theorem milli_milli_milli_sub : (1 : Millisecond.Offset) - (1 : Millisecond.Offset) = (0 : Millisecond.Offset) := rfl
theorem milli_sec_milli_sub : (1 : Millisecond.Offset) - (1 : Second.Offset) = (-999 : Millisecond.Offset) := rfl
theorem milli_min_milli_sub : (1 : Millisecond.Offset) - (1 : Minute.Offset) = (-59999 : Millisecond.Offset) := rfl
theorem milli_hour_milli_sub : (1 : Millisecond.Offset) - (1 : Hour.Offset) = (-3599999 : Millisecond.Offset) := rfl
theorem milli_day_milli_sub : (1 : Millisecond.Offset) - (1 : Day.Offset) = (-86399999 : Millisecond.Offset) := rfl
theorem milli_week_milli_sub : (1 : Millisecond.Offset) - (1 : Week.Offset) = (-604799999 : Millisecond.Offset) := rfl

theorem sec_nano_nano_sub : (1 : Second.Offset) - (1 : Nanosecond.Offset) = (999999999 : Nanosecond.Offset) := rfl
theorem sec_milli_milli_sub : (1 : Second.Offset) - (1 : Millisecond.Offset) = (999 : Millisecond.Offset) := rfl
theorem sec_sec_sec_sub : (1 : Second.Offset) - (1 : Second.Offset) = (0 : Second.Offset) := rfl
theorem sec_min_sec_sub : (1 : Second.Offset) - (1 : Minute.Offset) = (-59 : Second.Offset) := rfl
theorem sec_hour_sec_sub : (1 : Second.Offset) - (1 : Hour.Offset) = (-3599 : Second.Offset) := rfl
theorem sec_day_sec_sub : (1 : Second.Offset) - (1 : Day.Offset) = (-86399 : Second.Offset) := rfl
theorem sec_week_sec_sub : (1 : Second.Offset) - (1 : Week.Offset) = (-604799 : Second.Offset) := rfl

theorem min_nano_nano_sub : (1 : Minute.Offset) - (1 : Nanosecond.Offset) = (59999999999 : Nanosecond.Offset) := rfl
theorem min_milli_milli_sub : (1 : Minute.Offset) - (1 : Millisecond.Offset) = (59999 : Millisecond.Offset) := rfl
theorem min_sec_sec_sub : (1 : Minute.Offset) - (1 : Second.Offset) = (59 : Second.Offset) := rfl
theorem min_min_min_sub : (1 : Minute.Offset) - (1 : Minute.Offset) = (0 : Minute.Offset) := rfl
theorem min_hour_min_sub : (1 : Minute.Offset) - (1 : Hour.Offset) = (-59 : Minute.Offset) := rfl
theorem min_day_min_sub : (1 : Minute.Offset) - (1 : Day.Offset) = (-1439 : Minute.Offset) := rfl
theorem min_week_min_sub : (1 : Minute.Offset) - (1 : Week.Offset) = (-10079 : Minute.Offset) := rfl

theorem hour_nano_nano_sub : (1 : Hour.Offset) - (1 : Nanosecond.Offset) = (3599999999999 : Nanosecond.Offset) := rfl
theorem hour_milli_milli_sub : (1 : Hour.Offset) - (1 : Millisecond.Offset) = (3599999 : Millisecond.Offset) := rfl
theorem hour_sec_sec_sub : (1 : Hour.Offset) - (1 : Second.Offset) = (3599 : Second.Offset) := rfl
theorem hour_min_min_sub : (1 : Hour.Offset) - (1 : Minute.Offset) = (59 : Minute.Offset) := rfl
theorem hour_hour_hour_sub : (1 : Hour.Offset) - (1 : Hour.Offset) = (0 : Hour.Offset) := rfl
theorem hour_day_hour_sub : (1 : Hour.Offset) - (1 : Day.Offset) = (-23 : Hour.Offset) := rfl
theorem hour_week_hour_sub : (1 : Hour.Offset) - (1 : Week.Offset) = (-167 : Hour.Offset) := rfl

theorem day_nano_nano_sub : (1 : Day.Offset) - (1 : Nanosecond.Offset) = (86399999999999 : Nanosecond.Offset) := rfl
theorem day_milli_milli_sub : (1 : Day.Offset) - (1 : Millisecond.Offset) = (86399999 : Millisecond.Offset) := rfl
theorem day_sec_sec_sub : (1 : Day.Offset) - (1 : Second.Offset) = (86399 : Second.Offset) := rfl
theorem day_min_min_sub : (1 : Day.Offset) - (1 : Minute.Offset) = (1439 : Minute.Offset) := rfl
theorem day_hour_hour_sub : (1 : Day.Offset) - (1 : Hour.Offset) = (23 : Hour.Offset) := rfl
theorem day_day_day_sub : (1 : Day.Offset) - (1 : Day.Offset) = (0 : Day.Offset) := rfl
theorem day_week_day_sub : (1 : Day.Offset) - (1 : Week.Offset) = (-6 : Day.Offset) := rfl

theorem week_nano_nano_sub : (1 : Week.Offset) - (1 : Nanosecond.Offset) = (604799999999999 : Nanosecond.Offset) := rfl
theorem week_milli_milli_sub : (1 : Week.Offset) - (1 : Millisecond.Offset) = (604799999 : Millisecond.Offset) := rfl
theorem week_sec_sec_sub : (1 : Week.Offset) - (1 : Second.Offset) = (604799 : Second.Offset) := rfl
theorem week_min_min_sub : (1 : Week.Offset) - (1 : Minute.Offset) = (10079 : Minute.Offset) := rfl
theorem week_hour_hour_sub : (1 : Week.Offset) - (1 : Hour.Offset) = (167 : Hour.Offset) := rfl
theorem week_day_day_sub : (1 : Week.Offset) - (1 : Day.Offset) = (6 : Day.Offset) := rfl
theorem week_week_week_sub : (1 : Week.Offset) - (1 : Week.Offset) = (0 : Week.Offset) := rfl

/-
Of and To basic units
-/

example : (1 : Nanosecond.Offset).toInt = (1 : Int) := rfl
example : (1 : Millisecond.Offset).toInt = (1 : Int) := rfl
example : (1 : Second.Offset).toInt = (1 : Int) := rfl
example : (1 : Minute.Offset).toInt = (1 : Int) := rfl
example : (1 : Hour.Offset).toInt = (1 : Int) := rfl
example : (1 : Day.Offset).toInt = (1 : Int) := rfl
example : (1 : Week.Offset).toInt = (1 : Int) := rfl

example : Nanosecond.Offset.ofInt 1 = (1 : Nanosecond.Offset) := rfl
example : Millisecond.Offset.ofInt 1 = (1 : Millisecond.Offset) := rfl
example : Second.Offset.ofInt 1 = (1 : Second.Offset) := rfl
example : Minute.Offset.ofInt 1 = (1 : Minute.Offset) := rfl
example : Hour.Offset.ofInt 1 = (1 : Hour.Offset) := rfl
example : Day.Offset.ofInt 1 = (1 : Day.Offset) := rfl
example : Week.Offset.ofInt 1 = (1 : Week.Offset) := rfl

example : Nanosecond.Offset.ofNat 1 = (1 : Nanosecond.Offset) := rfl
example : Millisecond.Offset.ofNat 1 = (1 : Millisecond.Offset) := rfl
example : Second.Offset.ofNat 1 = (1 : Second.Offset) := rfl
example : Minute.Offset.ofNat 1 = (1 : Minute.Offset) := rfl
example : Hour.Offset.ofNat 1 = (1 : Hour.Offset) := rfl
example : Day.Offset.ofNat 1 = (1 : Day.Offset) := rfl
example : Week.Offset.ofNat 1 = (1 : Week.Offset) := rfl

example := Nanosecond.Ordinal.ofInt 1 (by decide)
example := Millisecond.Ordinal.ofInt 1 (by decide)
example := Second.Ordinal.ofInt (leap := false) 59 (by decide)
example := Second.Ordinal.ofInt (leap := true) 60 (by decide)
example := Minute.Ordinal.ofInt 1 (by decide)
example := Hour.Ordinal.ofInt 1 (by decide)
example := Day.Ordinal.ofInt 1 (by decide)
example := Week.Ordinal.ofInt 1 (by decide)

example := Nanosecond.Ordinal.ofFin 1
example := Millisecond.Ordinal.ofFin 1
example := Second.Ordinal.ofFin (leap := false) 37
example := Second.Ordinal.ofFin (leap := true) 37
example := Minute.Ordinal.ofFin 1
example := Hour.Ordinal.ofFin 1
example := Day.Ordinal.ofFin 1
example := Week.Ordinal.ofFin 1

example := Nanosecond.Ordinal.ofNat 1
example := Millisecond.Ordinal.ofNat 1
example := Second.Ordinal.ofNat (leap := false) 1
example := Second.Ordinal.ofNat (leap := true) 1
example := Minute.Ordinal.ofNat 1
example := Hour.Ordinal.ofNat 1
example := Day.Ordinal.ofNat 1
example := Week.Ordinal.ofNat 1

example := Nanosecond.Ordinal.toOffset 1
example := Millisecond.Ordinal.toOffset 1
example := Second.Ordinal.toOffset (leap := false) 1
example := Second.Ordinal.toOffset (leap := true) 1
example := Minute.Ordinal.toOffset 1
example := Hour.Ordinal.toOffset 1
example := Day.Ordinal.toOffset 1
example := Week.Ordinal.toOffset 1

example : (1 : Nanosecond.Ordinal).toInt = (1 : Int) := rfl
example : (1 : Millisecond.Ordinal).toInt = (1 : Int) := rfl
example : (1 : Second.Ordinal false).toInt = (1 : Int) := rfl
example : (1 : Second.Ordinal true).toInt = (1 : Int) := rfl
example : (1 : Minute.Ordinal).toInt = (1 : Int) := rfl
example : (1 : Hour.Ordinal).toInt = (1 : Int) := rfl
example : (1 : Day.Ordinal).toInt = (1 : Int) := rfl
example : (1 : Week.Ordinal).toInt = (1 : Int) := rfl

example : ((1 : Nanosecond.Ordinal).toFin (by decide) |>.val) = 1 := rfl
example : ((1 : Millisecond.Ordinal).toFin (by decide) |>.val) = 1 := rfl
example : ((1 : Second.Ordinal false).toFin (by decide) |>.val) = 1 := rfl
example : ((1 : Second.Ordinal true).toFin (by decide) |>.val) = 1 := rfl
example : ((1 : Minute.Ordinal).toFin (by decide) |>.val) = 1 := rfl
example : ((1 : Hour.Ordinal).toFin (by decide) |>.val) = 1 := rfl
example : ((1 : Day.Ordinal).toFin (by decide) |>.val) = 1 := rfl
example : ((1 : Week.Ordinal).toFin (by decide) |>.val) = 1 := rfl

example : (1 : Nanosecond.Ordinal).toNat = 1 := rfl
example : (1 : Millisecond.Ordinal).toNat = 1 := rfl
example : (1 : Second.Ordinal false).toNat = 1 := rfl
example : (1 : Second.Ordinal true).toNat = 1 := rfl
example : (1 : Minute.Ordinal).toNat = 1 := rfl
example : (1 : Hour.Ordinal).toNat = 1 := rfl
example : (1 : Day.Ordinal).toNat = 1 := rfl
example : (1 : Week.Ordinal).toNat = 1 := rfl

/--
info: 9
2023-06-10
2023-06-16
2023-07-09
2023-07-09
2024-06-09
2024-06-09
2023-06-08
2023-06-02
2023-05-09
2023-05-09
2022-06-09
2022-06-09
2023-06-01
2023-06-01
2023-06-11
2023-01-09
2023-01-09
0001-06-09
0001-06-09
23 2023 2023 2023 23 2023 2023 23 J
false
160
CE
2
2
Std.Time.Weekday.friday
23
2
06-09-2023
2023-06-09
2023-06-09
19517
1686268800000
1970-01-02

-/
#guard_msgs in
#eval do
  -- :>
  let date := date("2023-06-09")

  println! repr date.day
  println! date.addDays 1
  println! date.addWeeks 1
  println! date.addMonthsClip 1
  println! date.addMonthsRollOver 1
  println! date.addYearsClip 1
  println! date.addYearsRollOver 1

  println! date.subDays 1
  println! date.subWeeks 1
  println! date.subMonthsClip 1
  println! date.subMonthsRollOver 1
  println! date.subYearsClip 1
  println! date.subYearsRollOver 1

  println! date.withDaysClip 1
  println! date.withDaysRollOver 1
  println! date.withWeekday .sunday
  println! date.withMonthClip 1
  println! date.withMonthRollOver 1
  println! date.withYearClip 1
  println! date.withYearRollOver 1

  println! date.format "yy yyyy yyy yyy yy uuuu uuu uu MMMMM"
  println! date.inLeapYear
  println! date.dayOfYear
  println! date.era
  println! repr date.quarter
  println! repr date.alignedWeekOfMonth
  println! repr date.weekday
  println! repr date.weekOfYear
  println! repr date.weekOfMonth

  println! date.toAmericanDateString
  println! date.toLeanDateString
  println! date.toSQLDateString

  println! date.toDaysSinceUNIXEpoch
  println! date.toTimestampAssumingUTC
  println! PlainDate.ofDaysSinceUNIXEpoch 1

/--
info: 1997-03-19T02:03:04.000000000
1997-03-25T02:03:04.000000000
1997-04-18T02:03:04.000000000
1997-04-18T02:03:04.000000000
1998-03-18T02:03:04.000000000
1998-03-18T02:03:04.000000000
1997-03-17T02:03:04.000000000
1997-03-11T02:03:04.000000000
1997-02-18T02:03:04.000000000
1997-02-18T02:03:04.000000000
1996-03-18T02:03:04.000000000
1996-03-18T02:03:04.000000000
1997-03-01T02:03:04.000000000
1997-03-01T02:03:04.000000000
1997-03-23T02:03:04.000000000
1997-01-18T02:03:04.000000000
1997-01-18T02:03:04.000000000
0001-03-18T02:03:04.000000000
0001-03-18T02:03:04.000000000
97 1997 1997 1997 97 1997 1997 97 M
false
77
CE
1
4
Std.Time.Weekday.tuesday
12
3
9938
858650584000
1970-01-02T00:00:00.000000000

-/
#guard_msgs in
#eval do
  let plaindatetime := datetime("1997-03-18T02:03:04")

  println! plaindatetime.addDays 1
  println! plaindatetime.addWeeks 1
  println! plaindatetime.addMonthsClip 1
  println! plaindatetime.addMonthsRollOver 1
  println! plaindatetime.addYearsClip 1
  println! plaindatetime.addYearsRollOver 1

  println! plaindatetime.subDays 1
  println! plaindatetime.subWeeks 1
  println! plaindatetime.subMonthsClip 1
  println! plaindatetime.subMonthsRollOver 1
  println! plaindatetime.subYearsClip 1
  println! plaindatetime.subYearsRollOver 1

  println! plaindatetime.withDaysClip 1
  println! plaindatetime.withDaysRollOver 1
  println! plaindatetime.withWeekday .sunday
  println! plaindatetime.withMonthClip 1
  println! plaindatetime.withMonthRollOver 1
  println! plaindatetime.withYearClip 1
  println! plaindatetime.withYearRollOver 1

  println! plaindatetime.format "yy yyyy yyy yyy yy uuuu uuu uu MMMMM"
  println! plaindatetime.inLeapYear
  println! plaindatetime.dayOfYear
  println! plaindatetime.era
  println! repr plaindatetime.quarter
  println! repr plaindatetime.alignedWeekOfMonth
  println! repr plaindatetime.weekday
  println! repr plaindatetime.weekOfYear
  println! repr plaindatetime.weekOfMonth

  println! plaindatetime.toDaysSinceUNIXEpoch
  println! plaindatetime.toTimestampAssumingUTC
  println! PlainDateTime.ofDaysSinceUNIXEpoch 1 PlainTime.midnight

/--
info: 2024-09-13T02:01:02.000000000-03:00
2024-09-19T02:01:02.000000000-03:00
2024-10-12T02:01:02.000000000-03:00
2024-10-12T02:01:02.000000000-03:00
2025-09-12T02:01:02.000000000-03:00
2025-09-12T02:01:02.000000000-03:00
2024-09-11T02:01:02.000000000-03:00
2024-09-05T02:01:02.000000000-03:00
2024-08-12T02:01:02.000000000-03:00
2024-08-12T02:01:02.000000000-03:00
2023-09-12T02:01:02.000000000-03:00
2023-09-12T02:01:02.000000000-03:00
2024-09-01T02:01:02.000000000-03:00
2024-09-01T02:01:02.000000000-03:00
2024-09-15T02:01:02.000000000-03:00
2024-01-12T02:01:02.000000000-03:00
2024-01-12T02:01:02.000000000-03:00
0001-09-12T02:01:02.000000000-03:00
0001-09-12T02:01:02.000000000-03:00
24 2024 2024 2024 24 2024 2024 24 S
true
256
CE
3
3
Std.Time.Weekday.thursday
37
2
19978
1726117262000
1970-01-02T00:00:00.000000000Z

-/
#guard_msgs in
#eval do
  let zoned := DateTime.ofPlainDateTimeAssumingUTC datetime("2024-09-12T05:01:02") timezone("America/Sao_Paulo -03:00")

  println! zoned.addDays 1
  println! zoned.addWeeks 1
  println! zoned.addMonthsClip 1
  println! zoned.addMonthsRollOver 1
  println! zoned.addYearsClip 1
  println! zoned.addYearsRollOver 1

  println! zoned.subDays 1
  println! zoned.subWeeks 1
  println! zoned.subMonthsClip 1
  println! zoned.subMonthsRollOver 1
  println! zoned.subYearsClip 1
  println! zoned.subYearsRollOver 1

  println! zoned.withDaysClip 1
  println! zoned.withDaysRollOver 1
  println! zoned.withWeekday .sunday
  println! zoned.withMonthClip 1
  println! zoned.withMonthRollOver 1
  println! zoned.withYearClip 1
  println! zoned.withYearRollOver 1

  println! zoned.format "yy yyyy yyy yyy yy uuuu uuu uu MMMMM"
  println! zoned.inLeapYear
  println! zoned.dayOfYear
  println! zoned.era
  println! repr zoned.quarter
  println! repr zoned.alignedWeekOfMonth
  println! repr zoned.weekday
  println! repr zoned.weekOfYear
  println! repr zoned.weekOfMonth

  println! zoned.toDaysSinceUNIXEpoch
  println! zoned.toTimestamp
  println! DateTime.ofDaysSinceUNIXEpoch 1 PlainTime.midnight .UTC

/--
info: 1997-03-19T02:03:04.000000000[America/Sao_Paulo]
1997-03-25T02:03:04.000000000[America/Sao_Paulo]
1997-04-18T02:03:04.000000000[America/Sao_Paulo]
1997-04-18T02:03:04.000000000[America/Sao_Paulo]
1998-03-18T02:03:04.000000000[America/Sao_Paulo]
1998-03-18T02:03:04.000000000[America/Sao_Paulo]
1997-03-17T02:03:04.000000000[America/Sao_Paulo]
1997-03-17T02:03:04.000000000[America/Sao_Paulo]
1997-03-11T02:03:04.000000000[America/Sao_Paulo]
1997-02-18T02:03:04.000000000[America/Sao_Paulo]
1997-02-18T02:03:04.000000000[America/Sao_Paulo]
1996-03-18T02:03:04.000000000[America/Sao_Paulo]
1996-03-18T02:03:04.000000000[America/Sao_Paulo]
1997-03-01T02:03:04.000000000[America/Sao_Paulo]
1997-03-01T02:03:04.000000000[America/Sao_Paulo]
1997-03-23T02:03:04.000000000[America/Sao_Paulo]
1997-01-18T02:03:04.000000000[America/Sao_Paulo]
1997-01-18T02:03:04.000000000[America/Sao_Paulo]
0001-03-17T02:03:04.000000000[America/Sao_Paulo]
0001-03-17T02:03:04.000000000[America/Sao_Paulo]
97 1997 1997 1997 97 1997 1997 97 M
false
77
CE
1
4
Std.Time.Weekday.tuesday
12
3
9938
858661384000

-/
#guard_msgs in
#eval do
  let zoned := zoned("1997-03-18T02:03:04", sao_paulo)

  println! zoned.addDays 1
  println! zoned.addWeeks 1
  println! zoned.addMonthsClip 1
  println! zoned.addMonthsRollOver 1
  println! zoned.addYearsClip 1
  println! zoned.addYearsRollOver 1

  println! zoned.subDays 1
  println! zoned.subDays 1
  println! zoned.subWeeks 1
  println! zoned.subMonthsClip 1
  println! zoned.subMonthsRollOver 1
  println! zoned.subYearsClip 1
  println! zoned.subYearsRollOver 1

  println! zoned.withDaysClip 1
  println! zoned.withDaysRollOver 1
  println! zoned.withWeekday .sunday
  println! zoned.withMonthClip 1
  println! zoned.withMonthRollOver 1
  println! zoned.withYearClip 1
  println! zoned.withYearRollOver 1

  println! zoned.format "yy yyyy yyy yyy yy uuuu uuu uu MMMMM"
  println! zoned.inLeapYear
  println! zoned.dayOfYear
  println! zoned.era
  println! repr zoned.quarter
  println! repr zoned.alignedWeekOfMonth
  println! repr zoned.weekday
  println! repr zoned.weekOfYear
  println! repr zoned.weekOfMonth

  println! zoned.toDaysSinceUNIXEpoch
  println! zoned.toTimestamp

/--
info: 2023-06-09T00:00:00.000000000
0001-01-01T12:32:43.000000000
2033-11-18T12:32:43.000000000
-/
#guard_msgs in
#eval do
  println! PlainDateTime.ofPlainDate date("2023-06-09")
  println! PlainDateTime.ofPlainTime time("12:32:43")
  println! PlainDateTime.ofDaysSinceUNIXEpoch 23332 time("12:32:43")

/--
info: 1970-01-02T00:00:00.000000000Z
1997-03-18T00:00:00.000000000Z
1997-03-18T00:01:02.000000000Z
1997-03-18T00:01:02.000000000Z
2024-02-16T22:07:14.000000000Z

-/
#guard_msgs in
#eval do
  println! DateTime.ofDaysSinceUNIXEpoch 1 PlainTime.midnight .UTC
  println! DateTime.ofPlainDate date("1997-03-18") .UTC
  println! DateTime.ofPlainDateTime datetime("1997-03-18T00:01:02") .UTC
  println! DateTime.ofPlainDateTimeAssumingUTC datetime("1997-03-18T00:01:02") .UTC
  println! DateTime.ofTimestamp 1708121234 .UTC

/--
info: 1970-01-02T00:00:00.000000000[UTC]
1997-03-18T00:00:00.000000000[UTC]
1997-03-18T00:00:00.000000000[UTC]
1997-03-18T00:01:02.000000000[UTC]
1997-03-18T00:01:02.000000000[UTC]
1997-03-18T00:01:02.000000000[UTC]
2024-02-16T22:07:14.000000000[UTC]
2024-02-16T22:07:14.000000000[UTC]
-/
#guard_msgs in
#eval do
  println! ZonedDateTime.ofDaysSinceUNIXEpoch 1 PlainTime.midnight .UTC
  println! ZonedDateTime.ofPlainDate date("1997-03-18") .UTC
  println! ZonedDateTime.ofPlainDateWithZone date("1997-03-18") .UTC
  println! ZonedDateTime.ofPlainDateTime datetime("1997-03-18T00:01:02") .UTC
  println! ZonedDateTime.ofPlainDateTimeAssumingUTC datetime("1997-03-18T00:01:02") .UTC
  println! ZonedDateTime.ofPlainDateTimeWithZone datetime("1997-03-18T00:01:02") .UTC
  println! ZonedDateTime.ofTimestamp 1708121234 .UTC
  println! ZonedDateTime.ofTimestampWithZone 1708121234 .UTC
