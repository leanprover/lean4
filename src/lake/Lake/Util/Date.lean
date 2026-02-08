/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Init.Data.Ord.Basic
import Lake.Util.String
import Init.Data.String.Search
import Init.Data.Iterators.Consumers.Collect
import Init.Data.ToString.Macro

/-!
#  Date

A year-mont-day date. Used by Lake's TOML parser and its toolchain version
parser (for nightlies).
-/

namespace Lake

/-- A date (year-month-day). -/
public structure Date where
  year : Nat
  month : Nat
  day : Nat
  deriving Inhabited, DecidableEq, Ord, Repr

namespace Date

public instance : LT Date := ltOfOrd
public instance : LE Date := leOfOrd
public instance : Min Date := minOfLe
public instance : Max Date := maxOfLe

public abbrev IsLeapYear (y : Nat) : Prop :=
  y % 4 = 0 ∧ (y % 100 ≠ 0 ∨ y % 400 = 0)

public abbrev IsValidMonth (m : Nat) : Prop :=
  m ≥ 1 ∧ m ≤ 12

public def maxDay (y m : Nat) :  Nat :=
  if m = 2 then
    if IsLeapYear y then 29 else 28
  else if m ≤ 7 then
    30 + (m % 2)
  else
    31 - (m % 2)

public abbrev IsValidDay (y m d : Nat) : Prop :=
  d ≥ 1 ∧ d ≤ maxDay y m

public def ofValid? (year month day : Nat) : Option Date := do
  guard (IsValidMonth month ∧ IsValidDay year month day)
  return {year, month, day}

public def ofString? (t : String) : Option Date := do
  match t.split '-' |>.toList with
  | [y,m,d] =>
    ofValid? (← y.toNat?) (← m.toNat?) (← d.toNat?)
  | _ => none

public protected def toString (d : Date) : String :=
  s!"{zpad d.year 4}-{zpad d.month 2}-{zpad d.day 2}"

public instance : ToString Date := ⟨Date.toString⟩
