/-
Copyright (c) 2025 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Init.Prelude
public import Init.Data.String.Defs

public section

namespace Lean.Fmt

open Std

structure FullnessState where
  isFullBefore : Bool
  isFullAfter : Bool

abbrev FailureCond := FullnessState → Bool

inductive CoreDoc where
  | failure
  | newline
  | text (s : String)
  | either (a b : CoreDoc)
  | concat (a b : CoreDoc)
  | indent (n : Nat) (d : CoreDoc)
  | align (d : CoreDoc)
  | reset (d : CoreDoc)
  | full (d : CoreDoc)
with
  @[computed_field] isFailure : CoreDoc → FailureCond
    | .failure => fun _ => true
    | .newline => (·.isFullAfter)
    | .text s => fun
      | { isFullBefore := false, isFullAfter := false } => false
      | { isFullBefore := true, isFullAfter := false } => true
      | { isFullBefore := false, isFullAfter := true } => true
      | { isFullBefore := true, isFullAfter := true } => ! s.isEmpty
    | .full _ => (! ·.isFullAfter)
    | _ => fun _ => false
  @[computed_field] maxNewlineCount? : CoreDoc → Option Nat
    | .failure => none
    | .newline => some 1
    | .text _ => some 0
    | .either a b => .merge (max · ·) (maxNewlineCount? a) (maxNewlineCount? b)
    | .concat a b => .merge (· + ·) (maxNewlineCount? a) (maxNewlineCount? b)
    | .indent _ d
    | .align d
    | .reset d
    | .full d => maxNewlineCount? d

class Cost (τ : Type) extends Add τ, LE τ where
  textCost : (columnPos length : Nat) → τ
  newlineCost : (indentationAfterNewline : Nat) → τ
  optimalityCutoffWidth : Nat

  textCost_columnPos_monotone (cp₁ cp₂ n : Nat) :
    cp₁ ≤ cp₂ → textCost cp₁ n ≤ textCost cp₂ n
  textCost_length_add_decompose (cp n₁ n₂ : Nat) :
    textCost cp (n₁ + n₂) = textCost cp n₁ + textCost (cp + n₁) n₂
  newlineCost_monotone (i₁ i₂ : Nat) :
    i₁ ≤ i₂ → newlineCost i₁ ≤ newlineCost i₂

  add_zero (c : τ) : c + textCost 0 0 = c
  add_comm (c₁ c₂ : τ) : c₁ + c₂ = c₂ + c₁
  add_assoc (c₁ c₂ c₃ : τ) : (c₁ + c₂) + c₃ = c₁ + (c₂ + c₃)

  le_refl (c : τ) : c ≤ c
  le_trans (c₁ c₂ c₃ : τ) : c₁ ≤ c₂ → c₂ ≤ c₃ → c₁ ≤ c₃
  le_antisymm (c₁ c₂ : τ) : c₁ ≤ c₂ → c₂ ≤ c₁ → c₁ = c₂
  le_total (c₁ c₂ : τ) : c₁ ≤ c₂ ∨ c₂ ≤ c₁

  le_add_invariant (c₁ c₂ c₃ c₄ : τ) : c₁ ≤ c₂ → c₃ ≤ c₄ → c₁ + c₃ ≤ c₂ + c₄
