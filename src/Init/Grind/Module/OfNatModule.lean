/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
import Init.Grind.Module.Envelope

open Std

namespace Lean.Grind.IntModule.OfNatModule

/-!
Support for `NatModule` in the `grind` linear arithmetic module.
-/

theorem of_eq {α} [NatModule α] {a b : α} {a' b' : Q α}
    (h₁ : toQ a = a') (h₂ : toQ b = b') : a = b → a' = b' := by
  intro h; rw [← h₁, ← h₂, h]

theorem of_diseq {α} [NatModule α] [AddRightCancel α] {a b : α} {a' b' : Q α}
    (h₁ : toQ a = a') (h₂ : toQ b = b') : a ≠ b → a' ≠ b' := by
  rw [← h₁, ← h₂]; intro h₃ h₄; replace h₄ := toQ_inj h₄; contradiction

theorem of_le {α} [NatModule α] [LE α] [IsPreorder α] [OrderedAdd α] {a b : α} {a' b' : Q α}
    (h₁ : toQ a = a') (h₂ : toQ b = b') : a ≤ b → a' ≤ b' := by
  rw [← h₁, ← h₂, toQ_le]; intro; assumption

theorem of_not_le {α} [NatModule α] [LE α] [IsPreorder α] [OrderedAdd α] {a b : α} {a' b' : Q α}
    (h₁ : toQ a = a') (h₂ : toQ b = b') : ¬ a ≤ b → ¬ a' ≤ b' := by
  rw [← h₁, ← h₂, toQ_le]; intro; assumption

theorem of_lt {α} [NatModule α] [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α] [OrderedAdd α] {a b : α} {a' b' : Q α}
    (h₁ : toQ a = a') (h₂ : toQ b = b') : a < b → a' < b' := by
  rw [← h₁, ← h₂, toQ_lt]; intro; assumption

theorem of_not_lt {α} [NatModule α] [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α] [OrderedAdd α] {a b : α} {a' b' : Q α}
    (h₁ : toQ a = a') (h₂ : toQ b = b') : ¬ a < b → ¬ a' < b' := by
  rw [← h₁, ← h₂, toQ_lt]; intro; assumption

theorem add_congr {α} [NatModule α] {a b : α} {a' b' : Q α}
    (h₁ : toQ a = a') (h₂ : toQ b = b') : toQ (a + b) = a' + b' := by
  rw [toQ_add, h₁, h₂]

theorem smul_congr {α} [NatModule α] (n : Nat) (a : α) (i : Int) (a' : Q α)
    (h₁ : ↑n == i) (h₂ : toQ a = a') : toQ (n • a) = i • a' := by
  simp at h₁; rw [← h₁, ← h₂, toQ_smul]

end Lean.Grind.IntModule.OfNatModule
