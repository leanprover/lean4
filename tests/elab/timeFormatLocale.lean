import Std.Time
open Std.Time

/-!
Checks that `PlainDate.format` and `PlainDateTime.format` use the `locale` they are given for names
and localized weekday numbers, not only for the week fields, and that they agree with
`GenericFormat.format` under the same locale.
-/

def ptBR : DateFormat :=
  { DateFormat.enUS with
    firstDayOfWeek := .monday
    minimalDaysInFirstWeek := ⟨4, by decide⟩
    symbols := { DateFormat.enUS.symbols with
      monthLong := Vector.mk #["janeiro", "fevereiro", "março", "abril", "maio", "junho", "julho",
        "agosto", "setembro", "outubro", "novembro", "dezembro"] (by decide)
      weekdayLong := Vector.mk #["segunda-feira", "terça-feira", "quarta-feira", "quinta-feira",
        "sexta-feira", "sábado", "domingo"] (by decide) } }

-- 2024-03-17 is a Sunday: the 7th day of a Monday-first week, the 1st of a Sunday-first one.

/-- info: "domingo, 17 de março de 2024, e=7" -/
#guard_msgs in #eval date("2024-03-17").format "EEEE, d 'de' MMMM 'de' uuuu, 'e='e" ptBR

/-- info: "Sunday, 17 March 2024, e=1" -/
#guard_msgs in #eval date("2024-03-17").format "EEEE, d MMMM uuuu, 'e='e"

/-- info: "domingo 17 de março 13:45, c=7" -/
#guard_msgs in #eval datetime("2024-03-17T13:45:00").format "EEEE d 'de' MMMM HH:mm, 'c='c" ptBR

def localePattern : String := "EEEE e c cccc MMMM LLLL QQQQ w W Y G"

/-- info: true -/
#guard_msgs in
#eval
  let pdt := datetime("2024-03-17T13:45:00")
  let f : GenericFormat .any := GenericFormat.spec! localePattern { dateformat := ptBR }
  let viaGeneric := f.format (DateTime.ofPlainDateTimeWithZone pdt .UTC)
  pdt.format localePattern ptBR == viaGeneric && pdt.date.format localePattern ptBR == viaGeneric
