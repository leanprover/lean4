/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Util.Date

/-!
# TOML Date-Time

Defines data types for representing a TOML [date-time][1].
TOML date-times are based on [IETF RFC 3339][2] with some components
optionally left out, creating four distinct variants.

* **Offset Date-Time**: A full RFC 3339 date-time.
* **Local Date-Time**: An RFC 3339 date-time without the time zone.
* **Local Date**: The date portion of an RFC 3339 date-time (year-month-day).
* **Local Time**: The time portion of an RFC 3339 date-time (without time zone).

[1]: https://toml.io/en/v1.0.0#offset-date-time
[2]: https://datatracker.ietf.org/doc/html/rfc3339
-/

namespace Lake.Toml

/--
A TOML time (hour:minute:second.fraction).

We do not represent the whole time as seconds to due to the possibility
of leap seconds in RFC 3339 times.
-/
structure Time where
  hour : Nat
  minute : Nat
  second : Nat
  fracExponent : Nat := 0
  fracMantissa : Nat := 0
  deriving Inhabited, DecidableEq

namespace Time

abbrev IsValidHour (h : Nat) : Prop :=
  h ≤ 23

abbrev IsValidMinute (m : Nat) : Prop :=
  m ≤ 59

abbrev IsValidSecond (s : Nat) : Prop :=
  s ≤ 60

def zero : Time :=
  {hour := 0, minute := 0, second := 0}

instance : OfNat Time (nat_lit 0) := ⟨Time.zero⟩

def ofValid? (hour minute second : Nat) : Option Time := do
  guard (IsValidHour hour ∧ IsValidMinute minute ∧ IsValidSecond second)
  return {hour, minute, second}

def ofString? (t : String) : Option Time := do
  match t.split (· == ':') with
  | [h,m,s] =>
    match s.split (· == '.') with
    | [s,f] =>
      let time ← ofValid? (← h.toNat?) (← m.toNat?) (← s.toNat?)
      return {time with fracExponent := f.length-1, fracMantissa := ← f.toNat?}
    | [s] =>
      ofValid? (← h.toNat?) (← m.toNat?) (← s.toNat?)
    | _ => none
  | [h,m] =>
    ofValid? (← h.toNat?) (← m.toNat?) 0
  | _ => none

protected def toString (t : Time) : String :=
  let s := s!"{zpad t.hour 2}:{zpad t.minute 2}:{zpad t.second 2}"
  if t.fracMantissa = 0 then
    s
  else
    s!"{s}.{rpad (zpad t.fracMantissa t.fracExponent) '0' 3}"

instance : ToString Time := ⟨Time.toString⟩

end Time

/-- A TOML date-time. -/
inductive DateTime
| offsetDateTime (date : Date) (time : Time) (offset? : Option (Bool × Time) := none)
| localDateTime (date : Date) (time : Time)
| localDate (date : Date)
| localTime (time : Time)
deriving Inhabited, DecidableEq

instance : Coe Date DateTime := ⟨DateTime.localDate⟩
instance : Coe Time DateTime := ⟨DateTime.localTime⟩

namespace DateTime

def ofString? (dt : String) : Option DateTime := do
  match dt.split (fun c => c == 'T' || c == 't' || c == ' ') with
  | [d,t] =>
    let d ← Date.ofString? d
    if t.back == 'Z' || t.back == 'z' then
      return offsetDateTime d (← Time.ofString? <| t.dropRight 1)
    else if let [t,o] := t.split (· == '+') then
      return offsetDateTime d (← Time.ofString? t) (false, ← Time.ofString? o)
    else if let [t,o] := t.split (· == '-') then
      return offsetDateTime d (← Time.ofString? t) (true, ← Time.ofString? o)
    else
      return localDateTime d (← Time.ofString? t)
  | [x] =>
    if x.any (· == ':') then
      return localTime (← Time.ofString? x)
    else
      return localDate (← Date.ofString? x)
  | _ => none

protected def toString (dt : DateTime) : String :=
  match dt with
  | .offsetDateTime d t o? =>
    if let some (s,o) := o? then
      if s then
        s!"{d}T{t}-{zpad o.hour 2}:{zpad o.minute 2}"
      else
        s!"{d}T{t}+{zpad o.hour 2}:{zpad o.minute 2}"
    else
      s!"{d}T{t}Z"
  | .localDateTime d t => s!"{d}T{t}"
  | .localDate d => d.toString
  | .localTime t => t.toString

instance : ToString DateTime := ⟨DateTime.toString⟩

end DateTime
