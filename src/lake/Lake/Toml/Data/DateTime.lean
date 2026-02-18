/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Util.Date
import Lake.Util.String
import Init.Data.String.Search
import Init.Data.Iterators.Consumers.Collect
import Init.Data.Iterators.Consumers.Loop
import Init.Data.ToString.Macro

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
public structure Time where
  hour : Nat
  minute : Nat
  second : Nat
  fracExponent : Nat := 0
  fracMantissa : Nat := 0
  deriving Inhabited, DecidableEq

namespace Time

public abbrev IsValidHour (h : Nat) : Prop :=
  h ≤ 23

public abbrev IsValidMinute (m : Nat) : Prop :=
  m ≤ 59

public abbrev IsValidSecond (s : Nat) : Prop :=
  s ≤ 60

public def zero : Time :=
  {hour := 0, minute := 0, second := 0}

public instance : OfNat Time (nat_lit 0) := ⟨Time.zero⟩

public def ofValid? (hour minute second : Nat) : Option Time := do
  guard (IsValidHour hour ∧ IsValidMinute minute ∧ IsValidSecond second)
  return {hour, minute, second}

public def ofString? (t : String) : Option Time := do
  match t.split ':' |>.toList with
  | [h,m,s] =>
    match s.split '.' |>.toList with
    | [s,f] =>
      let time ← ofValid? (← h.toNat?) (← m.toNat?) (← s.toNat?)
      return {time with fracExponent := f.positions.length-1, fracMantissa := ← f.toNat?}
    | [s] =>
      ofValid? (← h.toNat?) (← m.toNat?) (← s.toNat?)
    | _ => none
  | [h,m] =>
    ofValid? (← h.toNat?) (← m.toNat?) 0
  | _ => none

public protected def toString (t : Time) : String :=
  let s := s!"{zpad t.hour 2}:{zpad t.minute 2}:{zpad t.second 2}"
  if t.fracMantissa = 0 then
    s
  else
    s!"{s}.{rpad (zpad t.fracMantissa t.fracExponent) '0' 3}"

public instance : ToString Time := ⟨Time.toString⟩

end Time

/-- A TOML date-time. -/
public inductive DateTime
| offsetDateTime (date : Date) (time : Time) (offset? : Option (Bool × Time) := none)
| localDateTime (date : Date) (time : Time)
| localDate (date : Date)
| localTime (time : Time)
deriving Inhabited, DecidableEq

public instance : Coe Date DateTime := ⟨DateTime.localDate⟩
public instance : Coe Time DateTime := ⟨DateTime.localTime⟩

namespace DateTime

public def ofString? (dt : String) : Option DateTime := do
  match dt.split (fun c => c == 'T' || c == 't' || c == ' ') |>.toList with
  | [d,t] =>
    let d ← Date.ofString? d.copy
    if t.back == 'Z' || t.back == 'z' then
      return offsetDateTime d (← Time.ofString? <| t.dropEnd 1 |>.copy)
    else if let [t,o] := t.split '+' |>.toStringList then
      return offsetDateTime d (← Time.ofString? t) <| some (false, ← Time.ofString? o)
    else if let [t,o] := t.split '-' |>.toStringList then
      return offsetDateTime d (← Time.ofString? t) <| some (true, ← Time.ofString? o)
    else
      return localDateTime d (← Time.ofString? t.copy)
  | [x] =>
    if x.contains ':' then
      return localTime (← Time.ofString? x.copy)
    else
      return localDate (← Date.ofString? x.copy)
  | _ => none

public protected def toString (dt : DateTime) : String :=
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

public instance : ToString DateTime := ⟨DateTime.toString⟩

end DateTime
