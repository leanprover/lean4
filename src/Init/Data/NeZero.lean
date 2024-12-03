/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
prelude
import Init.Data.Zero


/-!
# `NeZero` typeclass

We create a typeclass `NeZero n` which carries around the fact that `(n : R) ≠ 0`.

## Main declarations

* `NeZero`: `n ≠ 0` as a typeclass.
-/


variable {R : Type _} [Zero R]

/-- A type-class version of `n ≠ 0`.  -/
class NeZero (n : R) : Prop where
  /-- The proposition that `n` is not zero. -/
  out : n ≠ 0

theorem NeZero.ne (n : R) [h : NeZero n] : n ≠ 0 :=
  h.out

theorem NeZero.ne' (n : R) [h : NeZero n] : 0 ≠ n :=
  h.out.symm

theorem neZero_iff {n : R} : NeZero n ↔ n ≠ 0 :=
  ⟨fun h ↦ h.out, NeZero.mk⟩

@[simp] theorem neZero_zero_iff_false {α : Type _} [Zero α] : NeZero (0 : α) ↔ False :=
  ⟨fun _ ↦ NeZero.ne (0 : α) rfl, fun h ↦ h.elim⟩

instance {p : Prop} [Decidable p] {n m : Nat} [NeZero n] [NeZero m] :
    NeZero (if p then n else m) := by
  split <;> infer_instance
