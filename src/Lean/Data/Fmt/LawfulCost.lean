/-
Copyright (c) 2025 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Data.Fmt.Formatter
public import Init.Grind.Module.Basic
import Init

namespace Lean.Fmt

public class LawfulCost (τ : Type) [Add τ] [LE τ] extends Cost τ, Grind.AddCommMonoid τ, Std.IsLinearOrder τ where
  zero := textCost 0 0

  textCost_columnPos_monotone (cp₁ cp₂ n : Nat) :
    cp₁ ≤ cp₂ → textCost cp₁ n ≤ textCost cp₂ n
  textCost_length_add_decompose (cp n₁ n₂ : Nat) :
    textCost cp (n₁ + n₂) = textCost cp n₁ + textCost (cp + n₁) n₂
  newlineCost_monotone (i₁ i₂ : Nat) :
    i₁ ≤ i₂ → newlineCost i₁ ≤ newlineCost i₂

  le_add_invariant (c₁ c₂ c₃ c₄ : τ) : c₁ ≤ c₂ → c₃ ≤ c₄ → c₁ + c₃ ≤ c₂ + c₄

attribute [grind ext] DefaultCost

def DefaultCost.zero : DefaultCost w W :=
  ⟨0, 0⟩

instance : Zero (DefaultCost w W) where
  zero := DefaultCost.zero

theorem DefaultCost.zero_def : (0 : DefaultCost w W) = ⟨0, 0⟩ := by
  simp only [Zero.zero, OfNat.ofNat, DefaultCost.zero]

theorem DefaultCost.add_zero (c : DefaultCost w W) : c + 0 = c := by
  simp only [zero_def, add_def]
  grind

theorem DefaultCost.add_comm (c₁ c₂ : DefaultCost w W) : c₁ + c₂ = c₂ + c₁ := by
  simp only [add_def]
  grind

theorem DefaultCost.add_assoc (c₁ c₂ c₃ : DefaultCost w W) :
    (c₁ + c₂) + c₃ = c₁ + (c₂ + c₃) := by
  simp only [add_def]
  grind

instance : Grind.AddCommMonoid (DefaultCost w W) where
  zero := DefaultCost.zero
  add_zero := DefaultCost.add_zero
  add_comm := DefaultCost.add_comm
  add_assoc := DefaultCost.add_assoc

theorem DefaultCost.le_refl (c : DefaultCost w W) : c ≤ c := by
  simp only [le_def]
  grind

theorem DefaultCost.le_trans (c₁ c₂ c₃ : DefaultCost w W) : c₁ ≤ c₂ → c₂ ≤ c₃ → c₁ ≤ c₃ := by
  simp only [le_def]
  grind

theorem DefaultCost.le_antisymm (c₁ c₂ : DefaultCost w W) : c₁ ≤ c₂ → c₂ ≤ c₁ → c₁ = c₂ := by
  simp only [le_def]
  grind

theorem DefaultCost.le_total (c₁ c₂ : DefaultCost w W) : c₁ ≤ c₂ ∨ c₂ ≤ c₁ := by
  simp only [le_def]
  grind

instance : Std.IsLinearOrder (DefaultCost w W) where
  le_refl := DefaultCost.le_refl
  le_trans := DefaultCost.le_trans
  le_antisymm := DefaultCost.le_antisymm
  le_total := DefaultCost.le_total

theorem DefaultCost.textCost_columnPos_monotone
    (cp₁ cp₂ n : Nat) :
    cp₁ ≤ cp₂ →
    (Cost.textCost cp₁ n : DefaultCost w W) ≤
      Cost.textCost cp₂ n := by
  grind [= textCost_def, = le_def, Nat.mul_le_mul]

theorem DefaultCost.textCost_length_add_decompose (cp n₁ n₂ : Nat) :
    (Cost.textCost cp (n₁ + n₂) : DefaultCost w W) =
      Cost.textCost cp n₁ + Cost.textCost (cp + n₁) n₂ := by
  grind [= textCost_def, = add_def, Nat.sub_add_comm]

theorem DefaultCost.newlineCost_monotone (i₁ i₂ : Nat) :
    i₁ ≤ i₂ →
    (Cost.newlineCost i₁ : DefaultCost w W) ≤
      Cost.newlineCost i₂ := by
  grind [newlineCost_def]

def DefaultCost.le_add_invariant (c₁ c₂ c₃ c₄ : DefaultCost w W) : c₁ ≤ c₂ → c₃ ≤ c₄ → c₁ + c₃ ≤ c₂ + c₄ := by
  grind [= le_def, = add_def]

instance : LawfulCost (DefaultCost softWidth optimalityCutoffWidth) where
  textCost_columnPos_monotone := DefaultCost.textCost_columnPos_monotone
  textCost_length_add_decompose := DefaultCost.textCost_length_add_decompose
  newlineCost_monotone := DefaultCost.newlineCost_monotone

  le_add_invariant := DefaultCost.le_add_invariant
