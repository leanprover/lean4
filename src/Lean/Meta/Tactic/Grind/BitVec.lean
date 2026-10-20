/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
import Init.Grind
import Init.Data.BitVec.Basic
import Lean.Meta.LitValues
import Lean.ToExpr
import Lean.Meta.Tactic.Grind.Simp
public import Lean.Meta.Tactic.Grind.PropagatorAttr
public section
namespace Lean.Meta.Grind

/-!
Propagators that evaluate structural `BitVec` operations on literals.

The arguments are matched modulo equalities: given `x = 42#64`, the propagator for
`extractLsb'` asserts `BitVec.extractLsb' 63 32 x = 0#32`. The proofs combine the generic
congruence theorems `Grind.eval_congr₁`/`Grind.eval_congr₂` with an `Eq.refl` hypothesis
discharged by kernel reduction. Arguments that occur in the *result type* (widths, extract
bounds, `replicate` counts) must be syntactic literals; the remaining arguments only need to
be equal to literals.

We deliberately skip:
- arithmetic operations and comparisons (`+`, `*`, `-`, `/`, `%`, division variants, `<`, `≤`):
  they are handled by `cutsat`;
- `setWidth'` and `shiftLeftZeroExtend` (rare, and their argument order does not fit the
  suffix-application scheme used by the congruence theorems);
- `BitVec.cast`, `ofFin`/`toFin`.
-/

private def mkBVLit (n : Nat) (v : BitVec n) : GoalM Expr := do
  -- **Note**: `grind` uses `OfNat.ofNat` instead of `BitVec.ofNat` representation.
  shareCommon (← mkNumeral (mkApp (mkConst ``BitVec) (mkNatLit n)) v.toNat)

private def mkBoolLit (b : Bool) : GoalM Expr :=
  shareCommon (toExpr b)

/-- Returns the `BitVec` literal in the equivalence class root of `x`, if any. -/
private def getBV? (x : Expr) : GoalM (Option ((n : Nat) × BitVec n)) := do
  getBitVecValue? (← getRoot x)

/--
Given `e = f a` where the last argument `a` is matched modulo equalities, pushes `e = b`
where `b` is the literal computed by `eval` from `a`'s equivalence class root.
-/
private def unaryOp (e : Expr) (eval : Expr → GoalM (Option Expr)) : GoalM Unit := do
  let a := e.appArg!
  let aRoot ← getRoot a
  let some b ← eval aRoot | return ()
  internalize b 0
  let eType ← inferType e
  let proof := mkApp6 (mkConst ``Grind.eval_congr₁ [1, 1]) (← inferType a) eType e.appFn! a aRoot b
  let proof := mkApp2 proof (← mkEqProof a aRoot) (mkApp2 (mkConst ``Eq.refl [1]) eType b)
  pushEq e b proof

/--
Given `e = f a₁ a₂` where the last two arguments are matched modulo equalities, pushes
`e = b` where `b` is the literal computed by `eval` from the equivalence class roots.
-/
private def binOp (e : Expr) (eval : Expr → Expr → GoalM (Option Expr)) : GoalM Unit := do
  let a₂ := e.appArg!
  let a₁ := e.appFn!.appArg!
  let r₁ ← getRoot a₁
  let r₂ ← getRoot a₂
  let some b ← eval r₁ r₂ | return ()
  internalize b 0
  let eType ← inferType e
  let proof := mkApp9 (mkConst ``Grind.eval_congr₂ [1, 1, 1]) (← inferType a₁) (← inferType a₂) eType e.appFn!.appFn! a₁ r₁ a₂ r₂ b
  let proof := mkApp3 proof (← mkEqProof a₁ r₁) (← mkEqProof a₂ r₂) (mkApp2 (mkConst ``Eq.refl [1]) eType b)
  pushEq e b proof

/-- Table entry for `op : BitVec n → BitVec n` with head `declName` and the given arity. -/
@[inline] private def unaryBV (declName : Name) (arity : Nat)
    (op : {n : Nat} → BitVec n → BitVec n) (e : Expr) : GoalM Unit := do
  unless e.isAppOfArity declName arity do return ()
  unaryOp e fun r => do
    let some ⟨n, v⟩ ← getBitVecValue? r | return none
    some <$> mkBVLit n (op v)

/-- Table entry for `op : (m : Nat) → BitVec n → BitVec m` where `m` is argument 1. -/
@[inline] private def extendBV (declName : Name)
    (op : {n : Nat} → (m : Nat) → BitVec n → BitVec m) (e : Expr) : GoalM Unit := do
  unless e.isAppOfArity declName 3 do return ()
  let some m ← getNatValue? (e.getArg! 1) | return ()  -- occurs in the result type
  unaryOp e fun r => do
    let some ⟨_, v⟩ ← getBitVecValue? r | return none
    some <$> mkBVLit m (op m v)

/-- Table entry for extract-like `op : (i j : Nat) → BitVec n → BitVec m`. -/
@[inline] private def extractBV (declName : Name)
    (op : {n : Nat} → (i j : Nat) → BitVec n → (m : Nat) × BitVec m) (e : Expr) : GoalM Unit := do
  unless e.isAppOfArity declName 4 do return ()
  let some i ← getNatValue? (e.getArg! 1) | return ()  -- occurs in the result type
  let some j ← getNatValue? (e.getArg! 2) | return ()
  unaryOp e fun r => do
    let some ⟨_, v⟩ ← getBitVecValue? r | return none
    let ⟨m, w⟩ := op i j v
    some <$> mkBVLit m w

/-- Table entry for `op : BitVec n → BitVec n → BitVec n` (e.g. `&&&`) with a `BitVec` type guard. -/
@[inline] private def binBV (declName : Name) (arity : Nat)
    (op : {n : Nat} → BitVec n → BitVec n → BitVec n) (e : Expr) : GoalM Unit := do
  unless e.isAppOfArity declName arity do return ()
  binOp e fun r₁ r₂ => do
    let some ⟨n₁, v₁⟩ ← getBitVecValue? r₁ | return none
    let some ⟨n₂, v₂⟩ ← getBitVecValue? r₂ | return none
    if h : n₁ = n₂ then
      some <$> mkBVLit n₁ (op v₁ (h ▸ v₂))
    else
      return none

/-- Table entry for `op : BitVec n → Nat → BitVec n` (shifts, rotations). -/
@[inline] private def shiftBV (declName : Name) (arity : Nat)
    (op : {n : Nat} → BitVec n → Nat → BitVec n) (e : Expr) : GoalM Unit := do
  unless e.isAppOfArity declName arity do return ()
  binOp e fun r₁ r₂ => do
    let some ⟨n, v⟩ ← getBitVecValue? r₁ | return none
    let some i ← getNatValue? r₂ | return none
    some <$> mkBVLit n (op v i)

/-- Table entry for `op : BitVec n → Nat → Bool` (`getLsbD`, `getMsbD`). -/
@[inline] private def getBitBV (declName : Name)
    (op : {n : Nat} → BitVec n → Nat → Bool) (e : Expr) : GoalM Unit := do
  unless e.isAppOfArity declName 3 do return ()
  binOp e fun r₁ r₂ => do
    let some ⟨_, v⟩ ← getBitVecValue? r₁ | return none
    let some i ← getNatValue? r₂ | return none
    some <$> mkBoolLit (op v i)

/-! The table. -/

builtin_grind_propagator propagateBVNot ↑Complement.complement :=
  unaryBV ``Complement.complement 3 (~~~ ·)
builtin_grind_propagator propagateBVClz ↑BitVec.clz := unaryBV ``BitVec.clz 2 BitVec.clz
builtin_grind_propagator propagateBVCpop ↑BitVec.cpop := unaryBV ``BitVec.cpop 2 BitVec.cpop

builtin_grind_propagator propagateBVMsb ↑BitVec.msb := fun e => do
  unless e.isAppOfArity ``BitVec.msb 2 do return ()
  unaryOp e fun r => do
    let some ⟨_, v⟩ ← getBitVecValue? r | return none
    some <$> mkBoolLit v.msb

builtin_grind_propagator propagateBVToNat ↑BitVec.toNat := fun e => do
  unless e.isAppOfArity ``BitVec.toNat 2 do return ()
  unaryOp e fun r => do
    let some ⟨_, v⟩ ← getBitVecValue? r | return none
    some <$> shareCommon (mkNatLit v.toNat)

builtin_grind_propagator propagateBVToInt ↑BitVec.toInt := fun e => do
  unless e.isAppOfArity ``BitVec.toInt 2 do return ()
  unaryOp e fun r => do
    let some ⟨_, v⟩ ← getBitVecValue? r | return none
    some <$> shareCommon (mkIntLit v.toInt)

builtin_grind_propagator propagateBVOfNat ↑BitVec.ofNat := fun e => do
  unless e.isAppOfArity ``BitVec.ofNat 2 do return ()
  let some w ← getNatValue? (e.getArg! 0) | return ()  -- occurs in the result type
  unaryOp e fun r => do
    let some n ← getNatValue? r | return none
    some <$> mkBVLit w (BitVec.ofNat w n)

builtin_grind_propagator propagateBVOfInt ↑BitVec.ofInt := fun e => do
  unless e.isAppOfArity ``BitVec.ofInt 2 do return ()
  let some w ← getNatValue? (e.getArg! 0) | return ()  -- occurs in the result type
  unaryOp e fun r => do
    let some i ← getIntValue? r | return none
    some <$> mkBVLit w (BitVec.ofInt w i)

builtin_grind_propagator propagateBVSetWidth ↑BitVec.setWidth := extendBV ``BitVec.setWidth BitVec.setWidth
builtin_grind_propagator propagateBVSignExtend ↑BitVec.signExtend := extendBV ``BitVec.signExtend BitVec.signExtend

builtin_grind_propagator propagateBVExtractLsb' ↑BitVec.extractLsb' :=
  extractBV ``BitVec.extractLsb' fun start len v => ⟨len, v.extractLsb' start len⟩
builtin_grind_propagator propagateBVExtractLsb ↑BitVec.extractLsb :=
  extractBV ``BitVec.extractLsb fun hi lo v => ⟨hi - lo + 1, v.extractLsb hi lo⟩

builtin_grind_propagator propagateBVReplicate ↑BitVec.replicate := fun e => do
  unless e.isAppOfArity ``BitVec.replicate 3 do return ()
  let some i ← getNatValue? (e.getArg! 1) | return ()  -- occurs in the result type
  unaryOp e fun r => do
    let some ⟨n, v⟩ ← getBitVecValue? r | return none
    some <$> mkBVLit (n * i) (v.replicate i)

builtin_grind_propagator propagateBVAnd ↑HAnd.hAnd := binBV ``HAnd.hAnd 6 (· &&& ·)
builtin_grind_propagator propagateBVOr ↑HOr.hOr := binBV ``HOr.hOr 6 (· ||| ·)
builtin_grind_propagator propagateBVXor ↑HXor.hXor := binBV ``HXor.hXor 6 (· ^^^ ·)

builtin_grind_propagator propagateBVAppend ↑HAppend.hAppend := fun e => do
  unless e.isAppOfArity ``HAppend.hAppend 6 do return ()
  unless (← inferType e).isAppOf ``BitVec do return ()
  binOp e fun r₁ r₂ => do
    let some ⟨n₁, v₁⟩ ← getBitVecValue? r₁ | return none
    let some ⟨n₂, v₂⟩ ← getBitVecValue? r₂ | return none
    some <$> mkBVLit (n₁ + n₂) (v₁ ++ v₂)

builtin_grind_propagator propagateBVShiftLeft ↑BitVec.shiftLeft :=
  shiftBV ``BitVec.shiftLeft 3 BitVec.shiftLeft
builtin_grind_propagator propagateBVUShiftRight ↑BitVec.ushiftRight :=
  shiftBV ``BitVec.ushiftRight 3 BitVec.ushiftRight
builtin_grind_propagator propagateBVSShiftRight ↑BitVec.sshiftRight :=
  shiftBV ``BitVec.sshiftRight 3 BitVec.sshiftRight
builtin_grind_propagator propagateBVRotateLeft ↑BitVec.rotateLeft :=
  shiftBV ``BitVec.rotateLeft 3 BitVec.rotateLeft
builtin_grind_propagator propagateBVRotateRight ↑BitVec.rotateRight :=
  shiftBV ``BitVec.rotateRight 3 BitVec.rotateRight

/-- `x <<< i` and `x >>> i` where the shift amount is a `Nat` or a `BitVec`. -/
@[inline] private def hShiftBV (declName : Name)
    (op : {n : Nat} → BitVec n → Nat → BitVec n) (e : Expr) : GoalM Unit := do
  unless e.isAppOfArity declName 6 do return ()
  binOp e fun r₁ r₂ => do
    let some ⟨n, v⟩ ← getBitVecValue? r₁ | return none
    if let some i ← getNatValue? r₂ then
      some <$> mkBVLit n (op v i)
    else if let some ⟨_, w⟩ ← getBitVecValue? r₂ then
      some <$> mkBVLit n (op v w.toNat)
    else
      return none

builtin_grind_propagator propagateBVHShiftLeft ↑HShiftLeft.hShiftLeft :=
  hShiftBV ``HShiftLeft.hShiftLeft (· <<< ·)
builtin_grind_propagator propagateBVHShiftRight ↑HShiftRight.hShiftRight :=
  hShiftBV ``HShiftRight.hShiftRight (· >>> ·)

builtin_grind_propagator propagateBVGetLsbD ↑BitVec.getLsbD := getBitBV ``BitVec.getLsbD BitVec.getLsbD
builtin_grind_propagator propagateBVGetMsbD ↑BitVec.getMsbD := getBitBV ``BitVec.getMsbD BitVec.getMsbD

builtin_grind_propagator propagateBVGetElem ↑GetElem.getElem := fun e => do
  let_expr f@GetElem.getElem coll idx elem valid inst x i w := e | return ()
  unless inst.isAppOf ``BitVec.instGetElemNatBoolLt do return ()
  let iRoot ← getRoot i
  let some iv ← getNatValue? iRoot | return ()
  let xRoot ← getRoot x
  let some ⟨n, v⟩ ← getBitVecValue? xRoot | return ()
  unless iv < n do return ()
  let b ← mkBoolLit (v.getLsbD iv)
  internalize b 0
  -- `(fun w₂ : valid xRoot iRoot => Eq.refl b) : ∀ w₂, xRoot[iRoot]'w₂ = b` by kernel reduction
  let h₃ := mkLambda `w .default ((mkApp2 valid xRoot iRoot).headBeta)
    (mkApp2 (mkConst ``Eq.refl [1]) elem b)
  let proof := mkApp6 (mkConst ``Grind.getElem_congr f.constLevels!) coll idx elem valid inst x
  let proof := mkApp5 proof xRoot i iRoot w b
  let proof := mkApp3 proof (← mkEqProof x xRoot) (← mkEqProof i iRoot) h₃
  pushEq e b proof

end Lean.Meta.Grind
