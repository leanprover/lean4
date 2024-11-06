/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/

/-!
#  Date

A year-mont-day date. Used by Lake's TOML parser and its toolchain version
parser (for nightlies).
-/

namespace Lake

def lpad (s : String) (c : Char) (len : Nat) : String :=
  "".pushn c (len - s.length) ++ s

def rpad (s : String) (c : Char) (len : Nat) : String :=
  s.pushn c (len - s.length)

def zpad (n : Nat) (len : Nat) : String :=
  lpad (toString n) '0' len

/-- A date (year-month-day). -/
structure Date where
  year : Nat
  month : Nat
  day : Nat
  deriving Inhabited, DecidableEq, Ord, Repr

namespace Date

instance : LT Date := ltOfOrd
instance : LE Date := leOfOrd
instance : Min Date := minOfLe
instance : Max Date := maxOfLe

abbrev IsLeapYear (y : Nat) : Prop :=
  y % 4 = 0 ∧ (y % 100 ≠ 0 ∨ y % 400 = 0)

abbrev IsValidMonth (m : Nat) : Prop :=
  m ≥ 1 ∧ m ≤ 12

def maxDay (y m : Nat) :  Nat :=
  if m = 2 then
    if IsLeapYear y then 29 else 28
  else if m ≤ 7 then
    30 + (m % 2)
  else
    31 - (m % 2)

abbrev IsValidDay (y m d : Nat) : Prop :=
  d ≥ 1 ∧ d ≤ maxDay y m

def ofValid? (year month day : Nat) : Option Date := do
  guard (IsValidMonth month ∧ IsValidDay year month day)
  return {year, month, day}

def ofString? (t : String) : Option Date := do
  match t.split (· == '-') with
  | [y,m,d] =>
    ofValid? (← y.toNat?) (← m.toNat?) (← d.toNat?)
  | _ => none

protected def toString (d : Date) : String :=
  s!"{zpad d.year 4}-{zpad d.month 2}-{zpad d.day 2}"

instance : ToString Date := ⟨Date.toString⟩
