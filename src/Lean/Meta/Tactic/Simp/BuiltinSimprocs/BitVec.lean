/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.LitValues
import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Nat
import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Int
import Init.Data.BitVec.Basic

namespace BitVec
open Lean Meta Simp

/-- A bit-vector literal -/
structure Literal where
  /-- Size. -/
  n     : Nat
  /-- Actual value. -/
  value : BitVec n

/--
Try to convert `OfNat.ofNat`/`BitVec.OfNat` application into a
bitvector literal.
-/
def fromExpr? (e : Expr) : SimpM (Option Literal) := do
  let some ⟨n, value⟩ ← getBitVecValue? e | return none
  return some { n, value }

/--
Helper function for reducing homogenous unary bitvector operators.
-/
@[inline] def reduceUnary (declName : Name) (arity : Nat)
    (op : {n : Nat} → BitVec n → BitVec n) (e : Expr) : SimpM Step := do
  unless e.isAppOfArity declName arity do return .continue
  let some v ← fromExpr? e.appArg! | return .continue
  return .done { expr := toExpr (op v.value) }

/--
Helper function for reducing homogenous binary bitvector operators.
-/
@[inline] def reduceBin (declName : Name) (arity : Nat)
    (op : {n : Nat} → BitVec n → BitVec n → BitVec n) (e : Expr) : SimpM Step := do
  unless e.isAppOfArity declName arity do return .continue
  let some v₁ ← fromExpr? e.appFn!.appArg! | return .continue
  let some v₂ ← fromExpr? e.appArg! | return .continue
  if h : v₁.n = v₂.n then
    trace[Meta.debug] "reduce [{declName}] {v₁.value}, {v₂.value}"
    return .done { expr := toExpr (op v₁.value (h ▸ v₂.value)) }
  else
    return .continue

/-- Simplification procedure for `zeroExtend` and `signExtend` on `BitVec`s. -/
@[inline] def reduceExtend (declName : Name)
    (op : {n : Nat} → (m : Nat) → BitVec n → BitVec m) (e : Expr) : SimpM Step := do
  unless e.isAppOfArity declName 3 do return .continue
  let some v ← fromExpr? e.appArg! | return .continue
  let some n ← Nat.fromExpr? e.appFn!.appArg! | return .continue
  return .done { expr := toExpr (op n v.value) }

/--
Helper function for reducing bitvector functions such as `getLsb` and `getMsb`.
-/
@[inline] def reduceGetBit (declName : Name) (op : {n : Nat} → BitVec n → Nat → Bool) (e : Expr)
    : SimpM Step := do
  unless e.isAppOfArity declName 3 do return .continue
  let some v ← fromExpr? e.appFn!.appArg! | return .continue
  let some i ← Nat.fromExpr? e.appArg! | return .continue
  let b := op v.value i
  return .done { expr := toExpr b }

/--
Helper function for reducing bitvector functions such as `shiftLeft` and `rotateRight`.
-/
@[inline] def reduceShift (declName : Name) (arity : Nat)
    (op : {n : Nat} → BitVec n → Nat → BitVec n) (e : Expr) : SimpM Step := do
  unless e.isAppOfArity declName arity do return .continue
  let some v ← fromExpr? e.appFn!.appArg! | return .continue
  let some i ← Nat.fromExpr? e.appArg! | return .continue
  return .done { expr := toExpr (op v.value i) }

/--
Helper function for reducing bitvector predicates.
-/
@[inline] def reduceBinPred (declName : Name) (arity : Nat)
    (op : {n : Nat} → BitVec n → BitVec n → Bool) (e : Expr) (isProp := true) : SimpM Step := do
  unless e.isAppOfArity declName arity do return .continue
  let some v₁ ← fromExpr? e.appFn!.appArg! | return .continue
  let some v₂ ← fromExpr? e.appArg! | return .continue
  if h : v₁.n = v₂.n then
    let b := op v₁.value (h ▸ v₂.value)
    if isProp then
      evalPropStep e b
    else
      return .done { expr := toExpr b }
  else
    return .continue

/-- Simplification procedure for negation of `BitVec`s. -/
builtin_simproc [simp, seval] reduceNeg ((- _ : BitVec _)) := reduceUnary ``Neg.neg 3 (- ·)
/-- Simplification procedure for bitwise not of `BitVec`s. -/
builtin_simproc [simp, seval] reduceNot ((~~~ _ : BitVec _)) :=
  reduceUnary ``Complement.complement 3 (~~~ ·)
/-- Simplification procedure for absolute value of `BitVec`s. -/
builtin_simproc [simp, seval] reduceAbs (BitVec.abs _) := reduceUnary ``BitVec.abs 2 BitVec.abs
/-- Simplification procedure for bitwise and of `BitVec`s. -/
builtin_simproc [simp, seval] reduceAnd ((_ &&& _ : BitVec _)) := reduceBin ``HAnd.hAnd 6 (· &&& ·)
/-- Simplification procedure for bitwise or of `BitVec`s. -/
builtin_simproc [simp, seval] reduceOr ((_ ||| _ : BitVec _)) := reduceBin ``HOr.hOr 6 (· ||| ·)
/-- Simplification procedure for bitwise xor of `BitVec`s. -/
builtin_simproc [simp, seval] reduceXOr ((_ ^^^ _ : BitVec _)) := reduceBin ``HXor.hXor 6 (· ^^^ ·)
/-- Simplification procedure for addition of `BitVec`s. -/
builtin_simproc [simp, seval] reduceAdd ((_ + _ : BitVec _)) := reduceBin ``HAdd.hAdd 6 (· + ·)
/-- Simplification procedure for multiplication of `BitVec`s. -/
builtin_simproc [simp, seval] reduceMul ((_ * _ : BitVec _)) := reduceBin ``HMul.hMul 6 (· * ·)
/-- Simplification procedure for subtraction of `BitVec`s. -/
builtin_simproc [simp, seval] reduceSub ((_ - _ : BitVec _)) := reduceBin ``HSub.hSub 6 (· - ·)
/-- Simplification procedure for division of `BitVec`s. -/
builtin_simproc [simp, seval] reduceDiv ((_ / _ : BitVec _)) := reduceBin ``HDiv.hDiv 6 (· / ·)
/-- Simplification procedure for the modulo operation on `BitVec`s. -/
builtin_simproc [simp, seval] reduceMod ((_ % _ : BitVec _)) := reduceBin ``HMod.hMod 6 (· % ·)
/-- Simplification procedure for for the unsigned modulo operation on `BitVec`s. -/
builtin_simproc [simp, seval] reduceUMod ((umod _ _ : BitVec _)) := reduceBin ``umod 3 umod
/-- Simplification procedure for unsigned division of `BitVec`s. -/
builtin_simproc [simp, seval] reduceUDiv ((udiv _ _ : BitVec _)) := reduceBin ``udiv 3 udiv
/-- Simplification procedure for division of `BitVec`s using the SMT-Lib conventions. -/
builtin_simproc [simp, seval] reduceSMTUDiv ((smtUDiv _ _ : BitVec _)) := reduceBin ``smtUDiv 3 smtUDiv
/-- Simplification procedure for the signed modulo operation on `BitVec`s. -/
builtin_simproc [simp, seval] reduceSMod ((smod _ _ : BitVec _)) := reduceBin ``smod 3 smod
/-- Simplification procedure for signed remainder of `BitVec`s. -/
builtin_simproc [simp, seval] reduceSRem ((srem _ _ : BitVec _)) := reduceBin ``srem 3 srem
/-- Simplification procedure for signed t-division of `BitVec`s. -/
builtin_simproc [simp, seval] reduceSDiv ((sdiv _ _ : BitVec _)) := reduceBin ``sdiv 3 sdiv
/-- Simplification procedure for signed division of `BitVec`s using the SMT-Lib conventions. -/
builtin_simproc [simp, seval] reduceSMTSDiv ((smtSDiv _ _ : BitVec _)) := reduceBin ``smtSDiv 3 smtSDiv
/-- Simplification procedure for `getLsb` (lowest significant bit) on `BitVec`. -/
builtin_simproc [simp, seval] reduceGetLsb (getLsb _ _) := reduceGetBit ``getLsb getLsb
/-- Simplification procedure for `getMsb` (most significant bit) on `BitVec`. -/
builtin_simproc [simp, seval] reduceGetMsb (getMsb _ _) := reduceGetBit ``getMsb getMsb

/-- Simplification procedure for shift left on `BitVec`. -/
builtin_simproc [simp, seval] reduceShiftLeft (BitVec.shiftLeft _ _) :=
  reduceShift ``BitVec.shiftLeft 3 BitVec.shiftLeft
/-- Simplification procedure for unsigned shift right on `BitVec`. -/
builtin_simproc [simp, seval] reduceUShiftRight (BitVec.ushiftRight _ _) :=
  reduceShift ``BitVec.ushiftRight 3 BitVec.ushiftRight
/-- Simplification procedure for signed shift right on `BitVec`. -/
builtin_simproc [simp, seval] reduceSShiftRight (BitVec.sshiftRight _ _) :=
  reduceShift ``BitVec.sshiftRight 3 BitVec.sshiftRight
/-- Simplification procedure for shift left on `BitVec`. -/
builtin_simproc [simp, seval] reduceHShiftLeft ((_ <<< _ : BitVec _)) :=
  reduceShift ``HShiftLeft.hShiftLeft 6 (· <<< ·)
/-- Simplification procedure for shift right on `BitVec`. -/
builtin_simproc [simp, seval] reduceHShiftRight ((_ >>> _ : BitVec _)) :=
  reduceShift ``HShiftRight.hShiftRight 6 (· >>> ·)
/-- Simplification procedure for rotate left on `BitVec`. -/
builtin_simproc [simp, seval] reduceRotateLeft (BitVec.rotateLeft _ _) :=
  reduceShift ``BitVec.rotateLeft 3 BitVec.rotateLeft
/-- Simplification procedure for rotate right on `BitVec`. -/
builtin_simproc [simp, seval] reduceRotateRight (BitVec.rotateRight _ _) :=
  reduceShift ``BitVec.rotateRight 3 BitVec.rotateRight

/-- Simplification procedure for append on `BitVec`. -/
builtin_simproc [simp, seval] reduceAppend ((_ ++ _ : BitVec _)) := fun e => do
  unless e.isAppOfArity ``HAppend.hAppend 6 do return .continue
  let some v₁ ← fromExpr? e.appFn!.appArg! | return .continue
  let some v₂ ← fromExpr? e.appArg! | return .continue
  return .done { expr := toExpr (v₁.value ++ v₂.value) }

/-- Simplification procedure for casting `BitVec`s along an equality of the size. -/
builtin_simproc [simp, seval] reduceCast (cast _ _) := fun e => do
  unless e.isAppOfArity ``cast 4 do return .continue
  let some v ← fromExpr? e.appArg! | return .continue
  let some m ← Nat.fromExpr? e.appFn!.appFn!.appArg! | return .continue
  return .done { expr := toExpr (BitVec.ofNat m v.value.toNat) }

/-- Simplification procedure for `BitVec.toNat`. -/
builtin_simproc [simp, seval] reduceToNat (BitVec.toNat _) := fun e => do
  unless e.isAppOfArity ``BitVec.toNat 2 do return .continue
  let some v ← fromExpr? e.appArg! | return .continue
  return .done { expr := mkNatLit v.value.toNat }

/-- Simplification procedure for `BitVec.toInt`. -/
builtin_simproc [simp, seval] reduceToInt (BitVec.toInt _) := fun e => do
  unless e.isAppOfArity ``BitVec.toInt 2 do return .continue
  let some v ← fromExpr? e.appArg! | return .continue
  return .done { expr := toExpr v.value.toInt }

/-- Simplification procedure for `BitVec.ofInt`. -/
builtin_simproc [simp, seval] reduceOfInt (BitVec.ofInt _ _) := fun e => do
  unless e.isAppOfArity ``BitVec.ofInt 2 do return .continue
  let some n ← Nat.fromExpr? e.appFn!.appArg! | return .continue
  let some i ← Int.fromExpr? e.appArg! | return .continue
  return .done { expr := toExpr (BitVec.ofInt n i) }

/-- Simplification procedure for ensuring `BitVec.ofNat` literals are normalized. -/
builtin_simproc [simp, seval] reduceOfNat (BitVec.ofNat _ _) := fun e => do
  unless e.isAppOfArity ``BitVec.ofNat 2 do return .continue
  let some n ← Nat.fromExpr? e.appFn!.appArg! | return .continue
  let some v ← Nat.fromExpr? e.appArg! | return .continue
  let bv := BitVec.ofNat n v
  if bv.toNat == v then return .continue -- already normalized
  return .done { expr := toExpr (BitVec.ofNat n v) }

/-- Simplification procedure for `<` on `BitVec`s. -/
builtin_simproc [simp, seval] reduceLT (( _ : BitVec _) < _)  := reduceBinPred ``LT.lt 4 (· < ·)
/-- Simplification procedure for `≤` on `BitVec`s. -/
builtin_simproc [simp, seval] reduceLE (( _ : BitVec _) ≤ _)  := reduceBinPred ``LE.le 4 (. ≤ .)
/-- Simplification procedure for `>` on `BitVec`s. -/
builtin_simproc [simp, seval] reduceGT (( _ : BitVec _) > _)  := reduceBinPred ``GT.gt 4 (. > .)
/-- Simplification procedure for `≥` on `BitVec`s. -/
builtin_simproc [simp, seval] reduceGE (( _ : BitVec _) ≥ _)  := reduceBinPred ``GE.ge 4 (. ≥ .)

/-- Simplification procedure for unsigned less than `ult` on `BitVec`s. -/
builtin_simproc [simp, seval] reduceULT (BitVec.ult _ _) :=
  reduceBinPred ``BitVec.ult 3 BitVec.ult (isProp := false)
/-- Simplification procedure for unsigned less than or equal `ule` on `BitVec`s. -/
builtin_simproc [simp, seval] reduceULE (BitVec.ule _ _) :=
  reduceBinPred ``BitVec.ule 3 BitVec.ule (isProp := false)
/-- Simplification procedure for signed less than `slt` on `BitVec`s. -/
builtin_simproc [simp, seval] reduceSLT (BitVec.slt _ _) :=
  reduceBinPred ``BitVec.slt 3 BitVec.slt (isProp := false)
/-- Simplification procedure for signed less than or equal `sle` on `BitVec`s. -/
builtin_simproc [simp, seval] reduceSLE (BitVec.sle _ _) :=
  reduceBinPred ``BitVec.sle 3 BitVec.sle (isProp := false)

/-- Simplification procedure for `zeroExtend'` on `BitVec`s. -/
builtin_simproc [simp, seval] reduceZeroExtend' (zeroExtend' _ _) := fun e => do
  unless e.isAppOfArity ``zeroExtend' 4 do return .continue
  let some v ← fromExpr? e.appArg! | return .continue
  let some w ← Nat.fromExpr? e.appFn!.appFn!.appArg! | return .continue
  if h : v.n ≤ w then
    return .done { expr := toExpr (v.value.zeroExtend' h) }
  else
    return .continue

/-- Simplification procedure for `shiftLeftZeroExtend` on `BitVec`s. -/
builtin_simproc [simp, seval] reduceShiftLeftZeroExtend (shiftLeftZeroExtend _ _) := fun e => do
  unless e.isAppOfArity ``shiftLeftZeroExtend 3 do return .continue
  let some v ← fromExpr? e.appFn!.appArg! | return .continue
  let some m ← Nat.fromExpr? e.appArg! | return .continue
  return .done { expr := toExpr (v.value.shiftLeftZeroExtend m) }

/-- Simplification procedure for `extractLsb'` on `BitVec`s. -/
builtin_simproc [simp, seval] reduceExtracLsb' (extractLsb' _ _ _) := fun e => do
  unless e.isAppOfArity ``extractLsb' 4 do return .continue
  let some v ← fromExpr? e.appArg! | return .continue
  let some start ← Nat.fromExpr? e.appFn!.appFn!.appArg! | return .continue
  let some len ← Nat.fromExpr? e.appFn!.appArg! | return .continue
  return .done { expr := toExpr (v.value.extractLsb' start len) }

/-- Simplification procedure for `replicate` on `BitVec`s. -/
builtin_simproc [simp, seval] reduceReplicate (replicate _ _) := fun e => do
  unless e.isAppOfArity ``replicate 3 do return .continue
  let some v ← fromExpr? e.appArg! | return .continue
  let some w ← Nat.fromExpr? e.appFn!.appArg! | return .continue
  return .done { expr := toExpr (v.value.replicate w) }

/-- Simplification procedure for `zeroExtend` on `BitVec`s. -/
builtin_simproc [simp, seval] reduceZeroExtend (zeroExtend _ _) := reduceExtend ``zeroExtend zeroExtend

/-- Simplification procedure for `signExtend` on `BitVec`s. -/
builtin_simproc [simp, seval] reduceSignExtend (signExtend _ _) := reduceExtend ``signExtend signExtend

/-- Simplification procedure for `allOnes` -/
builtin_simproc [simp, seval] reduceAllOnes (allOnes _) := fun e => do
  unless e.isAppOfArity ``allOnes 1 do return .continue
  let some n ← Nat.fromExpr? e.appArg! | return .continue
  return .done { expr := toExpr (allOnes n) }

end BitVec
