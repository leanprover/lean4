/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude
public import Lean.Meta.AppBuilder
import Init.Data.String.Csimp

public section

namespace Lean.Meta

/--
Builds a proof of `String.ofList l₁ ≠ String.ofList l₂` for two distinct string literals.

The proof is `String.Internal.ofList_ne_ofList l₁ l₂ i (Eq.refl false)` where `i` is the first
position where the two strings differ. If one of them is a prefix of the other, `i` is the length
of the shorter one.

To check it, the kernel evaluates `String.Internal.charCodeAt i` at both lists, which traverses the
first `i` elements of each list without comparing them, and then compares two natural numbers.
It does not unfold `String.decEq`.
-/
def mkStringLitNeProof (s₁ s₂ : String) : MetaM Expr := do
  let l₁ := s₁.toList
  let l₂ := s₂.toList
  let i := firstDiff l₁ l₂ 0
  let h := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``false)
  return mkApp4 (mkConst ``String.Internal.ofList_ne_ofList) (toExpr l₁) (toExpr l₂) (mkRawNatLit i) h
where
  firstDiff : List Char → List Char → Nat → Nat
    | c₁ :: l₁, c₂ :: l₂, i => if c₁ == c₂ then firstDiff l₁ l₂ (i + 1) else i
    | _, _, i => i

end Lean.Meta
