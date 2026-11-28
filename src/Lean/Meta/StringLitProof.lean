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
Builds a proof of `s₁ ≠ s₂` for two distinct string literals.

The proof is `String.Internal.ne_of_sameByteAt s₁ s₂ i (Eq.refl false)` where `i` is the first
position where the UTF-8 encodings of the two strings differ. If one of them is a prefix of the
other, `i` is the size of the shorter one.

To check it, the kernel evaluates `String.Internal.sameByteAt i` on the bytes of the two literals,
which traverses the first `i` elements of the two lists simultaneously without comparing them, and
then compares the bytes at position `i`. It does not unfold `String.decEq`.
-/
def mkStringLitNeProof (s₁ s₂ : String) : MetaM Expr := do
  let i := firstDiff s₁.toUTF8 s₂.toUTF8 0
  let h := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``false)
  return mkApp4 (mkConst ``String.Internal.ne_of_sameByteAt) (mkStrLit s₁) (mkStrLit s₂) (mkRawNatLit i) h
where
  firstDiff (b₁ b₂ : ByteArray) (i : Nat) : Nat :=
    if h : i < b₁.size ∧ i < b₂.size then
      if b₁[i] == b₂[i] then firstDiff b₁ b₂ (i + 1) else i
    else i
  termination_by b₁.size - i

/--
Returns the code of the string `s`: the value of `String.Internal.byteCode s`.
See `String.Internal.codeOfBytes`.
-/
def stringLitCode (s : String) : Nat :=
  s.toUTF8.data.foldr (fun b n => b.toNat + 1 + 257 * n) 0

/--
Builds a proof of `String.Internal.byteCode s = n` for the string literal `s`, where `n` is the
numeral `stringLitCode s`. Returns `n` and the proof.

To check it, the kernel evaluates `String.Internal.codeOfBytes` on the list of bytes of `s`.
-/
def mkStringLitCodeProof (s : String) : Expr × Expr :=
  let n := mkRawNatLit (stringLitCode s)
  (n, mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) n)

end Lean.Meta
