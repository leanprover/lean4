/-
Copyright (c) 2022 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino
-/

example (h : Int) : Nat := by
  replace h : Nat := 0
  exact h

example (h : Nat) : Nat := by
  have h : Int := 0
  assumption -- original `h` is not absent but...

example (h : Nat) : Nat := by
  replace h : Int := 0
  fail_if_success assumption -- original `h` is absent now
  replace h : Nat := 0
  exact h

-- tests with `this`

example : Nat := by
  have : Int := 0
  replace : Nat := 0
  assumption

example : Nat := by
  have : Nat := 0
  have : Int := 0
  assumption -- original `this` is not absent but...

example : Nat := by
  have : Nat := 0
  replace : Int := 0
  fail_if_success assumption -- original `this` is absent now
  replace : Nat := 0
  assumption

-- trying to replace the type of a variable when the goal depends on it

example {a : Nat} : a = a := by
  replace a : Int := 0
  have : Nat := by assumption -- old `a` is not gone
  have : Int := by exact a    -- new `a` is of type `Int`
  simp
