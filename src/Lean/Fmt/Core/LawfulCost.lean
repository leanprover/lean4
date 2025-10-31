/-
Copyright (c) 2025 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.Core.Formatter
public import Init.Grind.Module.Basic
public import Init

/-!
This file documents the properties that a cost function in the `Fmt` formatter must fulfill
in order for formatting with the cost function to be correct and efficient.

The properties in this file have been taken from 'A Pretty Expressive Printer' [1] by
Sorawee Porncharoenwase, Justin Pombrio and Emina Torlak.

[1] https://arxiv.org/pdf/2310.01530
-/

namespace Lean.Fmt

/--
`LawfulCost` documents the properties that a cost function in the `Fmt` formatter mus fulfill
in order for formatting with the cost function to be correct and efficient.
-/
public class LawfulCost (τ : Type) [Add τ] [LE τ]
    extends Cost τ, Grind.AddCommMonoid τ, Std.IsLinearOrder τ where
  zero := textCost 0 0
  textCost_monotone (cp₁ cp₂ n : Nat) : cp₁ ≤ cp₂ → textCost cp₁ n ≤ textCost cp₂ n
  textCost_add (cp n₁ n₂ : Nat) : textCost cp (n₁ + n₂) = textCost cp n₁ + textCost (cp + n₁) n₂
  newlineCost_monotone (i₁ i₂ : Nat) : i₁ ≤ i₂ → newlineCost i₁ ≤ newlineCost i₂
  add_monotone (c₁ c₂ c₃ c₄ : τ) : c₁ ≤ c₂ → c₃ ≤ c₄ → c₁ + c₃ ≤ c₂ + c₄
