/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
import Init.Grind.Propagator
import Lean.Meta.LitValues
public import Lean.Meta.Tactic.Grind.PropagatorAttr
public section
namespace Lean.Meta.Grind

/-!
Evaluation of `Char.toNat`, `Char.val`, and `Char.ofNat` when the argument is equal to a
literal.
-/

/-- Propagates `x.toNat = n` when `x` is equal to a character literal `c` with code point `n`.
The proof is `congrArg Char.toNat (x = c)` followed by `Eq.refl n`, whose type `n = n` is
accepted for `c.toNat = n` by the kernel, which evaluates `c.toNat`. -/
builtin_grind_propagator propagateCharToNatUp ↑Char.toNat := fun e => do
  let_expr Char.toNat x := e | return ()
  let c := (← getRootENode x).self
  let some v ← getCharValue? c | return ()
  let n ← shareCommon (mkNatLit v.toNat)
  let h₁ ← mkCongrArg (mkConst ``Char.toNat) (← mkEqProof x c)
  let h := mkApp6 (mkConst ``Eq.trans [1]) Nat.mkType e (mkApp (mkConst ``Char.toNat) c) n h₁ (mkApp2 (mkConst ``Eq.refl [1]) Nat.mkType n)
  internalize n (← getGeneration e) e
  pushEq e n h

/-- Propagates `x.val = n` when `x` is equal to a character literal with code point `n`. See `propagateCharToNatUp`. -/
builtin_grind_propagator propagateCharValUp ↑Char.val := fun e => do
  let_expr Char.val x := e | return ()
  let c := (← getRootENode x).self
  let some v ← getCharValue? c | return ()
  let n ← shareCommon (← mkNumeral (mkConst ``UInt32) v.toNat)
  let h₁ ← mkCongrArg (mkConst ``Char.val) (← mkEqProof x c)
  let h := mkApp6 (mkConst ``Eq.trans [1]) (mkConst ``UInt32) e (mkApp (mkConst ``Char.val) c) n h₁ (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``UInt32) n)
  internalize n (← getGeneration e) e
  pushEq e n h

/-- Propagates `Char.ofNat n = c` when `n` is equal to a numeral and `c` is the corresponding
character literal. See `propagateCharToNatUp`. -/
builtin_grind_propagator propagateCharOfNatUp ↑Char.ofNat := fun e => do
  let_expr Char.ofNat n := e | return ()
  if e.isCharLit then return ()
  let k := (← getRootENode n).self
  let some v ← getNatValue? k | return ()
  let c ← shareCommon (toExpr (Char.ofNat v))
  let h₁ ← mkCongrArg (mkConst ``Char.ofNat) (← mkEqProof n k)
  let h := mkApp6 (mkConst ``Eq.trans [1]) (mkConst ``Char) e (mkApp (mkConst ``Char.ofNat) k) c h₁ (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Char) c)
  internalize c (← getGeneration e) e
  pushEq e c h

end Lean.Meta.Grind
