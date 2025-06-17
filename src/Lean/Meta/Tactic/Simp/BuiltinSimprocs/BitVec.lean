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
  deriving DecidableEq, Repr

/--
Try to convert `OfNat.ofNat`/`BitVec.OfNat` application into a
bitvector literal.
-/
def fromExpr? (e : Expr) : SimpM (Option Literal) := do
  let some ⟨n, value⟩ ← getBitVecValue? e | return none
  return some { n, value }

/--
Helper function for reducing homogeneous unary bitvector operators.
-/
@[inline] def reduceUnary (declName : Name) (arity : Nat)
    (op : {n : Nat} → BitVec n → BitVec n) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some v ← fromExpr? e.appArg! | return .continue
  return .done <| toExpr (op v.value)

/--
Helper function for reducing homogeneous binary bitvector operators.
-/
@[inline] def reduceBin (declName : Name) (arity : Nat)
    (op : {n : Nat} → BitVec n → BitVec n → BitVec n) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some v₁ ← fromExpr? e.appFn!.appArg! | return .continue
  let some v₂ ← fromExpr? e.appArg! | return .continue
  if h : v₁.n = v₂.n then
    return .done <| toExpr (op v₁.value (h ▸ v₂.value))
  else
    return .continue

/-- Simplification procedure for `setWidth`, `zeroExtend` and `signExtend` on `BitVec`s. -/
@[inline] def reduceExtend (declName : Name)
    (op : {n : Nat} → (m : Nat) → BitVec n → BitVec m) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName 3 do return .continue
  let some v ← fromExpr? e.appArg! | return .continue
  let some n ← Nat.fromExpr? e.appFn!.appArg! | return .continue
  return .done <| toExpr (op n v.value)

/--
Helper function for reducing bitvector functions such as `getLsb` and `getMsb`.
-/
@[inline] def reduceGetBit (declName : Name) (op : {n : Nat} → BitVec n → Nat → Bool) (e : Expr)
    : SimpM DStep := do
  unless e.isAppOfArity declName 3 do return .continue
  let some v ← fromExpr? e.appFn!.appArg! | return .continue
  let some i ← Nat.fromExpr? e.appArg! | return .continue
  let b := op v.value i
  return .done <| toExpr b

/--
Helper function for reducing bitvector functions such as `shiftLeft` and `rotateRight`.
-/
@[inline] def reduceShift (declName : Name) (arity : Nat)
    (op : {n : Nat} → BitVec n → Nat → BitVec n) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some v ← fromExpr? e.appFn!.appArg! | return .continue
  let some i ← Nat.fromExpr? e.appArg! | return .continue
  return .done <| toExpr (op v.value i)

/--
Helper function for reducing `x <<< i` and `x >>> i` where `i` is a bitvector literal,
into one that is a natural number literal.
-/
@[inline] def reduceShiftWithBitVecLit (declName : Name) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName 6 do return .continue
  let v := e.appFn!.appArg!
  let some i ← fromExpr? e.appArg! | return .continue
  return .visit (← mkAppM declName #[v, toExpr i.value.toNat])

/--
Helper function for reducing bitvector predicates.
-/
@[inline] def reduceBinPred (declName : Name) (arity : Nat)
    (op : {n : Nat} → BitVec n → BitVec n → Bool) (e : Expr) : SimpM Step := do
  unless e.isAppOfArity declName arity do return .continue
  let some v₁ ← fromExpr? e.appFn!.appArg! | return .continue
  let some v₂ ← fromExpr? e.appArg! | return .continue
  if h : v₁.n = v₂.n then
    let b := op v₁.value (h ▸ v₂.value)
    evalPropStep e b
  else
    return .continue

@[inline] def reduceBoolPred (declName : Name) (arity : Nat)
    (op : {n : Nat} → BitVec n → BitVec n → Bool) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some v₁ ← fromExpr? e.appFn!.appArg! | return .continue
  let some v₂ ← fromExpr? e.appArg! | return .continue
  if h : v₁.n = v₂.n then
    let b := op v₁.value (h ▸ v₂.value)
    return .done <| toExpr b
  else
    return .continue


/-- Simplification procedure for negation of `BitVec`s. -/
builtin_dsimproc [simp, seval] reduceNeg ((- _ : BitVec _)) := reduceUnary ``Neg.neg 3 (- ·)
/-- Simplification procedure for bitwise not of `BitVec`s. -/
builtin_dsimproc [simp, seval] reduceNot ((~~~ _ : BitVec _)) :=
  reduceUnary ``Complement.complement 3 (~~~ ·)
/-- Simplification procedure for absolute value of `BitVec`s. -/
builtin_dsimproc [simp, seval] reduceAbs (BitVec.abs _) := reduceUnary ``BitVec.abs 2 BitVec.abs
/-- Simplification procedure for bitwise and of `BitVec`s. -/
builtin_dsimproc [simp, seval] reduceAnd ((_ &&& _ : BitVec _)) := reduceBin ``HAnd.hAnd 6 (· &&& ·)
/-- Simplification procedure for bitwise or of `BitVec`s. -/
builtin_dsimproc [simp, seval] reduceOr ((_ ||| _ : BitVec _)) := reduceBin ``HOr.hOr 6 (· ||| ·)
/-- Simplification procedure for bitwise xor of `BitVec`s. -/
builtin_dsimproc [simp, seval] reduceXOr ((_ ^^^ _ : BitVec _)) := reduceBin ``HXor.hXor 6 (· ^^^ ·)
/-- Simplification procedure for addition of `BitVec`s. -/
builtin_dsimproc [simp, seval] reduceAdd ((_ + _ : BitVec _)) := reduceBin ``HAdd.hAdd 6 (· + ·)
/-- Simplification procedure for multiplication of `BitVec`s. -/
builtin_dsimproc [simp, seval] reduceMul ((_ * _ : BitVec _)) := reduceBin ``HMul.hMul 6 (· * ·)
/-- Simplification procedure for subtraction of `BitVec`s. -/
builtin_dsimproc [simp, seval] reduceSub ((_ - _ : BitVec _)) := reduceBin ``HSub.hSub 6 (· - ·)
/-- Simplification procedure for division of `BitVec`s. -/
builtin_dsimproc [simp, seval] reduceDiv ((_ / _ : BitVec _)) := reduceBin ``HDiv.hDiv 6 (· / ·)
/-- Simplification procedure for the modulo operation on `BitVec`s. -/
builtin_dsimproc [simp, seval] reduceMod ((_ % _ : BitVec _)) := reduceBin ``HMod.hMod 6 (· % ·)
/-- Simplification procedure for the unsigned modulo operation on `BitVec`s. -/
builtin_dsimproc [simp, seval] reduceUMod ((umod _ _ : BitVec _)) := reduceBin ``umod 3 umod
/-- Simplification procedure for unsigned division of `BitVec`s. -/
builtin_dsimproc [simp, seval] reduceUDiv ((udiv _ _ : BitVec _)) := reduceBin ``udiv 3 udiv
/-- Simplification procedure for division of `BitVec`s using the SMT-LIB conventions. -/
builtin_dsimproc [simp, seval] reduceSMTUDiv ((smtUDiv _ _ : BitVec _)) := reduceBin ``smtUDiv 3 smtUDiv
/-- Simplification procedure for the signed modulo operation on `BitVec`s. -/
builtin_dsimproc [simp, seval] reduceSMod ((smod _ _ : BitVec _)) := reduceBin ``smod 3 smod
/-- Simplification procedure for signed remainder of `BitVec`s. -/
builtin_dsimproc [simp, seval] reduceSRem ((srem _ _ : BitVec _)) := reduceBin ``srem 3 srem
/-- Simplification procedure for signed t-division of `BitVec`s. -/
builtin_dsimproc [simp, seval] reduceSDiv ((sdiv _ _ : BitVec _)) := reduceBin ``sdiv 3 sdiv
/-- Simplification procedure for signed division of `BitVec`s using the SMT-LIB conventions. -/
builtin_dsimproc [simp, seval] reduceSMTSDiv ((smtSDiv _ _ : BitVec _)) := reduceBin ``smtSDiv 3 smtSDiv
/-- Simplification procedure for `getLsb` (lowest significant bit) on `BitVec`. -/
builtin_dsimproc [simp, seval] reduceGetLsb (getLsbD _ _) := reduceGetBit ``getLsbD getLsbD
/-- Simplification procedure for `getMsb` (most significant bit) on `BitVec`. -/
builtin_dsimproc [simp, seval] reduceGetMsb (getMsbD _ _) := reduceGetBit ``getMsbD getMsbD

/-- Simplification procedure for `getElem`  on `BitVec`. -/
builtin_dsimproc [simp, seval] reduceGetElem ((_ : BitVec _)[_]) := fun e => do
  let_expr getElem _coll _idx _elem _valid _inst v i _h  := e | return .continue
  let some v ← fromExpr? v | return .continue
  let some i ← Nat.fromExpr? i | return .continue
  let b := v.value.getLsbD i
  return .done <| toExpr b

/-- Simplification procedure for shift left on `BitVec`. -/
builtin_dsimproc [simp, seval] reduceShiftLeft (BitVec.shiftLeft _ _) :=
  reduceShift ``BitVec.shiftLeft 3 BitVec.shiftLeft
/-- Simplification procedure for unsigned shift right on `BitVec`. -/
builtin_dsimproc [simp, seval] reduceUShiftRight (BitVec.ushiftRight _ _) :=
  reduceShift ``BitVec.ushiftRight 3 BitVec.ushiftRight
/-- Simplification procedure for signed shift right on `BitVec`. -/
builtin_dsimproc [simp, seval] reduceSShiftRight (BitVec.sshiftRight _ _) :=
  reduceShift ``BitVec.sshiftRight 3 BitVec.sshiftRight
/-- Simplification procedure for shift left on `BitVec`. -/
builtin_dsimproc [simp, seval] reduceHShiftLeft ((_ <<< _ : BitVec _)) :=
  reduceShift ``HShiftLeft.hShiftLeft 6 (· <<< ·)
/-- Simplification procedure for converting a shift with a bit-vector literal into a natural number literal. -/
builtin_dsimproc [simp, seval] reduceHShiftLeft' ((_ <<< (_ : BitVec _) : BitVec _)) :=
  reduceShiftWithBitVecLit ``HShiftLeft.hShiftLeft
/-- Simplification procedure for shift right on `BitVec`. -/
builtin_dsimproc [simp, seval] reduceHShiftRight ((_ >>> _ : BitVec _)) :=
  reduceShift ``HShiftRight.hShiftRight 6 (· >>> ·)
/-- Simplification procedure for converting a shift with a bit-vector literal into a natural number literal. -/
builtin_dsimproc [simp, seval] reduceHShiftRight' ((_ >>> (_ : BitVec _) : BitVec _)) :=
  reduceShiftWithBitVecLit ``HShiftRight.hShiftRight
/-- Simplification procedure for rotate left on `BitVec`. -/
builtin_dsimproc [simp, seval] reduceRotateLeft (BitVec.rotateLeft _ _) :=
  reduceShift ``BitVec.rotateLeft 3 BitVec.rotateLeft
/-- Simplification procedure for rotate right on `BitVec`. -/
builtin_dsimproc [simp, seval] reduceRotateRight (BitVec.rotateRight _ _) :=
  reduceShift ``BitVec.rotateRight 3 BitVec.rotateRight

/-- Simplification procedure for append on `BitVec`. -/
builtin_dsimproc [simp, seval] reduceAppend ((_ ++ _ : BitVec _)) := fun e => do
  let_expr HAppend.hAppend _ _ _ _ a b ← e | return .continue
  let some v₁ ← fromExpr? a | return .continue
  let some v₂ ← fromExpr? b | return .continue
  return .done <| toExpr (v₁.value ++ v₂.value)

/-- Simplification procedure for casting `BitVec`s along an equality of the size. -/
builtin_dsimproc [simp, seval] reduceCast (cast _ _) := fun e => do
  let_expr cast _ m _ v ← e | return .continue
  let some v ← fromExpr? v | return .continue
  let some m ← Nat.fromExpr? m | return .continue
  return .done <| toExpr (BitVec.ofNat m v.value.toNat)

/-- Simplification procedure for `BitVec.toNat`. -/
builtin_dsimproc [simp, seval] reduceToNat (BitVec.toNat _) := fun e => do
  let_expr BitVec.toNat _ v ← e | return .continue
  let some v ← fromExpr? v | return .continue
  return .done <| mkNatLit v.value.toNat

/-- Simplification procedure for `BitVec.toInt`. -/
builtin_dsimproc [simp, seval] reduceToInt (BitVec.toInt _) := fun e => do
  let_expr BitVec.toInt _ v ← e | return .continue
  let some v ← fromExpr? v | return .continue
  return .done <| toExpr v.value.toInt

/-- Simplification procedure for `BitVec.ofInt`. -/
builtin_dsimproc [simp, seval] reduceOfInt (BitVec.ofInt _ _) := fun e => do
  let_expr BitVec.ofInt n i ← e | return .continue
  let some n ← Nat.fromExpr? n | return .continue
  let some i ← Int.fromExpr? i | return .continue
  return .done <| toExpr (BitVec.ofInt n i)

/-- Simplification procedure for ensuring `BitVec.ofNat` literals are normalized. -/
builtin_dsimproc [simp, seval] reduceOfNat (BitVec.ofNat _ _) := fun e => do
  let_expr BitVec.ofNat n v ← e | return .continue
  let some n ← Nat.fromExpr? n | return .continue
  let some v ← Nat.fromExpr? v | return .continue
  let bv := BitVec.ofNat n v
  if bv.toNat == v then return .continue -- already normalized
  return .done <| toExpr (BitVec.ofNat n v)

/-- Simplification procedure for `=` on `BitVec`s. -/
builtin_simproc [simp, seval] reduceEq  (( _ : BitVec _) = _)  := reduceBinPred ``Eq 3 (. = .)
/-- Simplification procedure for `≠` on `BitVec`s. -/
builtin_simproc [simp, seval] reduceNe  (( _ : BitVec _) ≠ _)  := reduceBinPred ``Ne 3 (. ≠ .)
/-- Simplification procedure for `==` on `BitVec`s. -/
builtin_dsimproc [simp, seval] reduceBEq  (( _ : BitVec _) == _)  :=
  reduceBoolPred ``BEq.beq 4 (· == ·)
/-- Simplification procedure for `!=` on `BitVec`s. -/
builtin_dsimproc [simp, seval] reduceBNe  (( _ : BitVec _) != _)  :=
  reduceBoolPred ``bne 4 (· != ·)

/-- Simplification procedure for `<` on `BitVec`s. -/
builtin_simproc [simp, seval] reduceLT (( _ : BitVec _) < _)  := reduceBinPred ``LT.lt 4 (· < ·)
/-- Simplification procedure for `≤` on `BitVec`s. -/
builtin_simproc [simp, seval] reduceLE (( _ : BitVec _) ≤ _)  := reduceBinPred ``LE.le 4 (. ≤ .)
/-- Simplification procedure for `>` on `BitVec`s. -/
builtin_simproc [simp, seval] reduceGT (( _ : BitVec _) > _)  := reduceBinPred ``GT.gt 4 (. > .)
/-- Simplification procedure for `≥` on `BitVec`s. -/
builtin_simproc [simp, seval] reduceGE (( _ : BitVec _) ≥ _)  := reduceBinPred ``GE.ge 4 (. ≥ .)

/-- Simplification procedure for unsigned less than `ult` on `BitVec`s. -/
builtin_dsimproc [simp, seval] reduceULT (BitVec.ult _ _) :=
  reduceBoolPred ``BitVec.ult 3 BitVec.ult
/-- Simplification procedure for unsigned less than or equal `ule` on `BitVec`s. -/
builtin_dsimproc [simp, seval] reduceULE (BitVec.ule _ _) :=
  reduceBoolPred ``BitVec.ule 3 BitVec.ule
/-- Simplification procedure for signed less than `slt` on `BitVec`s. -/
builtin_dsimproc [simp, seval] reduceSLT (BitVec.slt _ _) :=
  reduceBoolPred ``BitVec.slt 3 BitVec.slt
/-- Simplification procedure for signed less than or equal `sle` on `BitVec`s. -/
builtin_dsimproc [simp, seval] reduceSLE (BitVec.sle _ _) :=
  reduceBoolPred ``BitVec.sle 3 BitVec.sle

/-- Simplification procedure for `setWidth'` on `BitVec`s. -/
builtin_dsimproc [simp, seval] reduceSetWidth' (setWidth' _ _) := fun e => do
  let_expr setWidth' _ w _ v ← e | return .continue
  let some v ← fromExpr? v | return .continue
  let some w ← Nat.fromExpr? w | return .continue
  if h : v.n ≤ w then
    return .done <| toExpr (v.value.setWidth' h)
  else
    return .continue

/-- Simplification procedure for `shiftLeftZeroExtend` on `BitVec`s. -/
builtin_dsimproc [simp, seval] reduceShiftLeftZeroExtend (shiftLeftZeroExtend _ _) := fun e => do
  let_expr shiftLeftZeroExtend _ v m ← e | return .continue
  let some v ← fromExpr? v | return .continue
  let some m ← Nat.fromExpr? m | return .continue
  return .done <| toExpr (v.value.shiftLeftZeroExtend m)

/-- Simplification procedure for `extractLsb'` on `BitVec`s. -/
builtin_dsimproc [simp, seval] reduceExtracLsb' (extractLsb' _ _ _) := fun e => do
  let_expr extractLsb' _ start len v ← e | return .continue
  let some v ← fromExpr? v | return .continue
  let some start ← Nat.fromExpr? start | return .continue
  let some len ← Nat.fromExpr? len | return .continue
  return .done <| toExpr (v.value.extractLsb' start len)

/-- Simplification procedure for `replicate` on `BitVec`s. -/
builtin_dsimproc [simp, seval] reduceReplicate (replicate _ _) := fun e => do
  let_expr replicate _ i v ← e | return .continue
  let some v ← fromExpr? v | return .continue
  let some i ← Nat.fromExpr? i | return .continue
  return .done <| toExpr (v.value.replicate i)

/-- Simplification procedure for `setWidth` on `BitVec`s. -/
builtin_dsimproc [simp, seval] reduceSetWidth (setWidth _ _) := reduceExtend ``setWidth setWidth

/-- Simplification procedure for `zeroExtend` on `BitVec`s. -/
builtin_dsimproc [simp, seval] reduceZeroExtend (zeroExtend _ _) := reduceExtend ``zeroExtend zeroExtend

/-- Simplification procedure for `signExtend` on `BitVec`s. -/
builtin_dsimproc [simp, seval] reduceSignExtend (signExtend _ _) := reduceExtend ``signExtend signExtend

/-- Simplification procedure for `allOnes` -/
builtin_dsimproc [simp, seval] reduceAllOnes (allOnes _) := fun e => do
  let_expr allOnes n ← e | return .continue
  let some n ← Nat.fromExpr? n | return .continue
  return .done <| toExpr (allOnes n)

builtin_dsimproc [simp, seval] reduceBitVecOfFin (BitVec.ofFin _)  := fun e => do
  let_expr BitVec.ofFin w v ← e | return .continue
  let some w ← evalNat w |>.run | return .continue
  let some ⟨_, v⟩ ← getFinValue? v | return .continue
  return .done <| toExpr (BitVec.ofNat w v.val)

builtin_dsimproc [simp, seval] reduceBitVecToFin (BitVec.toFin _)  := fun e => do
  let_expr BitVec.toFin _ v ← e | return .continue
  let some ⟨_, v⟩ ← getBitVecValue? v | return .continue
  return .done <| toExpr v.toFin

/--
Helper function for reducing `(x <<< i) <<< j` (and `(x >>> i) >>> j`) where `i` and `j` are
natural number literals.
-/
@[inline] def reduceShiftShift (declName : Name) (thmName : Name) (e : Expr) : SimpM Step := do
  unless e.isAppOfArity declName 6 do return .continue
  let aux := e.appFn!.appArg!
  let some i ← Nat.fromExpr? e.appArg! | return .continue
  unless aux.isAppOfArity declName 6 do return .continue
  let x := aux.appFn!.appArg!
  let some j ← Nat.fromExpr? aux.appArg! | return .continue
  let i_add_j := toExpr (i + j)
  let expr ← mkAppM declName #[x, i_add_j]
  let proof ← mkAppM thmName #[x, aux.appArg!, e.appArg!]
  let proof ← mkEqSymm proof -- we rewrite (x <<< i) <<< j ↦ x <<< (i + j) [the opposite direction]
  return .visit { expr, proof? := some proof }

builtin_simproc reduceShiftLeftShiftLeft (((_ <<< _ : BitVec _) <<< _ : BitVec _)) :=
  reduceShiftShift ``HShiftLeft.hShiftLeft ``shiftLeft_add
builtin_simproc reduceShiftRightShiftRight (((_ >>> _ : BitVec _) >>> _ : BitVec _)) :=
  reduceShiftShift ``HShiftRight.hShiftRight ``shiftRight_add

end BitVec
