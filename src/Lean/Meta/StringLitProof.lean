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

To check it, the kernel evaluates `String.Internal.sameCharAt i l₁ l₂`, which traverses the first
`i` elements of the two lists simultaneously without comparing them, and then compares the
characters at position `i`. It does not unfold `String.decEq`.
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

/--
Returns the code of the string `s`: the value of `String.Internal.code s`.
See `String.Internal.codeOfList`.
-/
def stringLitCode (s : String) : Nat :=
  s.toList.foldr (fun c n => c.toNat + 1 + 2097152 * n) 0

/--
Builds a proof of `String.Internal.code s = n` for the string literal `s`, where `n` is the
numeral `stringLitCode s`. Returns `n` and the proof.

To check it, the kernel evaluates `String.Internal.codeOfList` on the list of characters of `s`.
-/
def mkStringLitCodeProof (s : String) : Expr × Expr :=
  let n := mkRawNatLit (stringLitCode s)
  let h := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) n
  (n, mkApp3 (mkConst ``String.Internal.code_ofList) (toExpr s.toList) n h)

end Lean.Meta
