@[reducible]
def isLeapYear (y : Nat) : Prop :=  (y % 400 = 0) ∨ (y % 4 = 0 ∧ y % 100 ≠ 0)

def daysInMonth (year : Nat) (month : Nat) : Nat :=
  match month with
  | 2  => if isLeapYear year then 29 else 28
  | 4  => 30
  | 6  => 30
  | 9  => 30
  | 11 => 30
  | _  => 31

/-
Stuck at:
year : Nat
⊢ (match 4 with
  | 2 => if isLeapYear year then 29 else 28
  | 4 => 30
  | 6 => 30
  | 9 => 30
  | 11 => 30
  | x => 31) =
  30
-/
example (year : Nat) : daysInMonth year 4 = 30 := by
  simp [daysInMonth]

example (year : Nat) : daysInMonth year 12 = 31 := by
  delta daysInMonth
  simp

example (year : Nat) : daysInMonth year 2 = (if isLeapYear year then 29 else 28) := by
  simp [daysInMonth]

def f : Char → Nat → Nat
 | 'a', _ => 1
 | 'b', _ => 2
 | _, _   => 3

example : f 'a' n = 1 := by
  simp[f]

example : f 'b' n = 2 := by
  simp[f]

example : f 'c' n = 3 := by
  simp (config := { decide := true }) [f]

def g : String → Nat → Nat
 | "hello", _ => 1
 | "world", _ => 2
 | _, _       => 3

example : g "hello" n = 1 := by
  simp[g]

example : g "world" n = 2 := by
  simp[g]

example : g "abc" n = 3 := by
  simp (config := { decide := true }) [g]

def fn : Fin 8 → Nat → Nat
 | 2, _ => 1
 | 3, _ => 2
 | _, _ => 3

example : fn 2 n = 1 := by
  simp [fn]

example : fn 4 n = 3 := by
  simp [fn]

def f8 : UInt8 → Nat → Nat
 | 10, _ => 1
 | 20, _ => 2
 | _, _  => 3

example : f8 10 n = 1 := by
  simp [f8]

example : f8 30 n = 3 := by
  simp [f8]

def f16 : UInt16 → Nat → Nat
 | 10, _ => 1
 | 20, _ => 2
 | _, _  => 3

example : f16 10 n = 1 := by
  simp [f16]

example : f16 30 n = 3 := by
  simp [f16]

def f32 : UInt32 → Nat → Nat
 | 10, _ => 1
 | 20, _ => 2
 | _, _  => 3

example : f32 10 n = 1 := by
  simp [f32]

example : f32 30 n = 3 := by
  simp [f32]

def f64 : UInt64 → Nat → Nat
 | 10, _ => 1
 | 20, _ => 2
 | _, _  => 3

example : f64 10 n = 1 := by
  simp [f64]

example : f64 30 n = 3 := by
  simp [f64]
