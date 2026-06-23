/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.DSimp.DSimpM
import Lean.Meta.Sym.LitValues
namespace Lean.Meta.Sym.DSimp

/-!
# Ground Term Evaluation for `Sym.dsimp`

This module provides simplification procedures (`Simproc`) for evaluating ground terms
of builtin types. It is designed for the `Sym.dsimp` simplifier and addresses
performance issues in the standard `Meta.Simp` simprocs.
-/

def skipIfUnchanged (e : Expr) (result : Result) : Result :=
  match result with
  | .step e' done => if isSameExpr e e' then .rfl done else result
  | _ => result

abbrev evalUnary [ToExpr α] (toValue? : Expr → Option α) (op : α → α) (a : Expr) : DSimpM Result := do
  let some a := toValue? a | return .rfl
  let e ← share <| toExpr (op a)
  return .step e (done := true)

abbrev evalUnaryNat : (op : Nat → Nat) → (a : Expr) → DSimpM Result := evalUnary getNatValue?
abbrev evalUnaryInt : (op : Int → Int) → (a : Expr) → DSimpM Result := evalUnary getIntValue?
abbrev evalUnaryRat : (op : Rat → Rat) → (a : Expr) → DSimpM Result := evalUnary getRatValue?
abbrev evalUnaryUInt8 : (op : UInt8 → UInt8) → (a : Expr) → DSimpM Result := evalUnary getUInt8Value?
abbrev evalUnaryUInt16 : (op : UInt16 → UInt16) → (a : Expr) → DSimpM Result := evalUnary getUInt16Value?
abbrev evalUnaryUInt32 : (op : UInt32 → UInt32) → (a : Expr) → DSimpM Result := evalUnary getUInt32Value?
abbrev evalUnaryUInt64 : (op : UInt64 → UInt64) → (a : Expr) → DSimpM Result := evalUnary getUInt64Value?
abbrev evalUnaryInt8 : (op : Int8 → Int8) → (a : Expr) → DSimpM Result := evalUnary getInt8Value?
abbrev evalUnaryInt16 : (op : Int16 → Int16) → (a : Expr) → DSimpM Result := evalUnary getInt16Value?
abbrev evalUnaryInt32 : (op : Int32 → Int32) → (a : Expr) → DSimpM Result := evalUnary getInt32Value?
abbrev evalUnaryInt64 : (op : Int64 → Int64) → (a : Expr) → DSimpM Result := evalUnary getInt64Value?

abbrev evalUnaryFin' (op : {n : Nat} → Fin n → Fin n) (a : Expr) : DSimpM Result := do
  let some a := getFinValue? a | return .rfl
  let e ← share <| toExpr (op a.val)
  return .step e (done := true)

abbrev evalUnaryBitVec' (op : {n : Nat} → BitVec n → BitVec n) (a : Expr) : DSimpM Result := do
  let some a := getBitVecValue? a | return .rfl
  let e ← share <| toExpr (op a.val)
  return .step e (done := true)

abbrev evalBin [ToExpr α] (toValue? : Expr → Option α) (op : α → α → α) (a b : Expr) : DSimpM Result := do
  let some a := toValue? a | return .rfl
  let some b := toValue? b | return .rfl
  let e ← share <| toExpr (op a b)
  return .step e (done := true)

abbrev evalBinNat : (op : Nat → Nat → Nat) → (a b : Expr) → DSimpM Result := evalBin getNatValue?
abbrev evalBinInt : (op : Int → Int → Int) → (a b : Expr) → DSimpM Result := evalBin getIntValue?
abbrev evalBinRat : (op : Rat → Rat → Rat) → (a b : Expr) → DSimpM Result := evalBin getRatValue?
abbrev evalBinUInt8 : (op : UInt8 → UInt8 → UInt8) → (a b : Expr) → DSimpM Result := evalBin getUInt8Value?
abbrev evalBinUInt16 : (op : UInt16 → UInt16 → UInt16) → (a b : Expr) → DSimpM Result := evalBin getUInt16Value?
abbrev evalBinUInt32 : (op : UInt32 → UInt32 → UInt32) → (a b : Expr) → DSimpM Result := evalBin getUInt32Value?
abbrev evalBinUInt64 : (op : UInt64 → UInt64 → UInt64) → (a b : Expr) → DSimpM Result := evalBin getUInt64Value?
abbrev evalBinInt8 : (op : Int8 → Int8 → Int8) → (a b : Expr) → DSimpM Result := evalBin getInt8Value?
abbrev evalBinInt16 : (op : Int16 → Int16 → Int16) → (a b : Expr) → DSimpM Result := evalBin getInt16Value?
abbrev evalBinInt32 : (op : Int32 → Int32 → Int32) → (a b : Expr) → DSimpM Result := evalBin getInt32Value?
abbrev evalBinInt64 : (op : Int64 → Int64 → Int64) → (a b : Expr) → DSimpM Result := evalBin getInt64Value?

abbrev evalBinFin' (op : {n : Nat} → Fin n → Fin n → Fin n) (a b : Expr) : DSimpM Result := do
  let some a := getFinValue? a | return .rfl
  let some b := getFinValue? b | return .rfl
  if h : a.n = b.n then
    let e ← share <| toExpr (op a.val (h ▸ b.val))
    return .step e (done := true)
  else
    return .rfl

abbrev evalBinBitVec' (op : {n : Nat} → BitVec n → BitVec n → BitVec n) (a b : Expr) : DSimpM Result := do
  let some a := getBitVecValue? a | return .rfl
  let some b := getBitVecValue? b | return .rfl
  if h : a.n = b.n then
    let e ← share <| toExpr (op a.val (h ▸ b.val))
    return .step e (done := true)
  else
    return .rfl

abbrev evalPowNat [ToExpr α] (maxExponent : Nat) (toValue? : Expr → Option α) (op : α → Nat → α) (a b : Expr) : DSimpM Result := do
  let some a := toValue? a | return .rfl
  let some b := getNatValue? b | return .rfl
  if b > maxExponent then return .rfl
  let e ← share <| toExpr (op a b)
  return .step e (done := true)

abbrev evalPowInt [ToExpr α] (maxExponent : Nat) (toValue? : Expr → Option α) (op : α → Int → α) (a b : Expr) : DSimpM Result := do
  let some a := toValue? a | return .rfl
  let some b := getIntValue? b | return .rfl
  if b.natAbs > maxExponent then return .rfl
  let e ← share <| toExpr (op a b)
  return .step e (done := true)

macro "declare_eval_bin" id:ident op:term : command =>
  `(def $id:ident (α : Expr) (a b : Expr) : DSimpM Result :=
  match_expr α with
  | Nat => evalBinNat $op a b
  | Int => evalBinInt $op a b
  | Rat => evalBinRat $op a b
  | Fin _ => evalBinFin' $op a b
  | BitVec _ => evalBinBitVec' $op a b
  | UInt8 => evalBinUInt8 $op a b
  | UInt16 => evalBinUInt16 $op a b
  | UInt32 => evalBinUInt32 $op a b
  | UInt64 => evalBinUInt64 $op a b
  | Int8 => evalBinInt8 $op a b
  | Int16 => evalBinInt16 $op a b
  | Int32 => evalBinInt32 $op a b
  | Int64 => evalBinInt64 $op a b
  | _ => return .rfl
  )

declare_eval_bin evalAdd (· + ·)
declare_eval_bin evalSub (· - ·)
declare_eval_bin evalMul (· * ·)

def evalDiv (e : Expr) (α : Expr) (a b : Expr) : DSimpM Result :=
  match_expr α with
  | Nat => evalBinNat (. / .) a b
  | Int => evalBinInt (. / .) a b
  | Rat => return skipIfUnchanged e (← evalBinRat (. / .) a b)
  | Fin _ => evalBinFin' (. / .) a b
  | BitVec _ => evalBinBitVec' (. / .) a b
  | UInt8 => evalBinUInt8 (. / .) a b
  | UInt16 => evalBinUInt16 (. / .) a b
  | UInt32 => evalBinUInt32 (. / .) a b
  | UInt64 => evalBinUInt64 (. / .) a b
  | Int8 => evalBinInt8 (. / .) a b
  | Int16 => evalBinInt16 (. / .) a b
  | Int32 => evalBinInt32 (. / .) a b
  | Int64 => evalBinInt64 (. / .) a b
  | _ => return .rfl

def evalMod (α : Expr) (a b : Expr) : DSimpM Result :=
  match_expr α with
  | Nat => evalBinNat (· % ·) a b
  | Int => evalBinInt (· % ·) a b
  | Fin _ => evalBinFin' (· % ·) a b
  | BitVec _ => evalBinBitVec' (· % ·) a b
  | UInt8 => evalBinUInt8 (· % ·) a b
  | UInt16 => evalBinUInt16 (· % ·) a b
  | UInt32 => evalBinUInt32 (· % ·) a b
  | UInt64 => evalBinUInt64 (· % ·) a b
  | Int8 => evalBinInt8 (· % ·) a b
  | Int16 => evalBinInt16 (· % ·) a b
  | Int32 => evalBinInt32 (· % ·) a b
  | Int64 => evalBinInt64 (· % ·) a b
  | _ => return .rfl

def evalNeg (α : Expr) (a : Expr) : DSimpM Result :=
  match_expr α with
  | Int => evalUnaryInt (- ·) a
  | Rat => evalUnaryRat (- ·) a
  | Fin _ => evalUnaryFin' (- ·) a
  | BitVec _ => evalUnaryBitVec' (- ·) a
  | UInt8 => evalUnaryUInt8 (- ·) a
  | UInt16 => evalUnaryUInt16 (- ·) a
  | UInt32 => evalUnaryUInt32 (- ·) a
  | UInt64 => evalUnaryUInt64 (- ·) a
  | Int8 => evalUnaryInt8 (- ·) a
  | Int16 => evalUnaryInt16 (- ·) a
  | Int32 => evalUnaryInt32 (- ·) a
  | Int64 => evalUnaryInt64 (- ·) a
  | _ => return .rfl

def evalComplement (α : Expr) (a : Expr) : DSimpM Result :=
  match_expr α with
  | Int => evalUnaryInt (~~~ ·) a
  | BitVec _ => evalUnaryBitVec' (~~~ ·) a
  | UInt8 => evalUnaryUInt8 (~~~ ·) a
  | UInt16 => evalUnaryUInt16 (~~~ ·) a
  | UInt32 => evalUnaryUInt32 (~~~ ·) a
  | UInt64 => evalUnaryUInt64 (~~~ ·) a
  | Int8 => evalUnaryInt8 (~~~ ·) a
  | Int16 => evalUnaryInt16 (~~~ ·) a
  | Int32 => evalUnaryInt32 (~~~ ·) a
  | Int64 => evalUnaryInt64 (~~~ ·) a
  | _ => return .rfl

def evalInv (α : Expr) (a : Expr) : DSimpM Result :=
  match_expr α with
  | Rat => evalUnaryRat (· ⁻¹) a
  | _ => return .rfl

macro "declare_eval_bin_bitwise" id:ident op:term : command =>
  `(def $id:ident (α : Expr) (a b : Expr) : DSimpM Result :=
  match_expr α with
  | Nat => evalBinNat $op a b
  | Fin _ => evalBinFin' $op a b
  | BitVec _ => evalBinBitVec' $op a b
  | UInt8 => evalBinUInt8 $op a b
  | UInt16 => evalBinUInt16 $op a b
  | UInt32 => evalBinUInt32 $op a b
  | UInt64 => evalBinUInt64 $op a b
  | Int8 => evalBinInt8 $op a b
  | Int16 => evalBinInt16 $op a b
  | Int32 => evalBinInt32 $op a b
  | Int64 => evalBinInt64 $op a b
  | _ => return .rfl
  )

declare_eval_bin_bitwise evalAnd (· &&& ·)
declare_eval_bin_bitwise evalOr (· ||| ·)
declare_eval_bin_bitwise evalXOr (· ^^^ ·)

def evalPow (maxExponent : Nat) (α β : Expr) (a b : Expr) : DSimpM Result :=
  match_expr β with
  | Nat => match_expr α with
    | Nat => evalPowNat maxExponent getNatValue? (· ^ ·) a b
    | Int => evalPowNat maxExponent getIntValue? (· ^ ·) a b
    | Rat => evalPowNat maxExponent getRatValue? (· ^ ·) a b
    | UInt8 => evalPowNat maxExponent getUInt8Value? (· ^ ·) a b
    | UInt16 => evalPowNat maxExponent getUInt16Value? (· ^ ·) a b
    | UInt32 => evalPowNat maxExponent getUInt32Value? (· ^ ·) a b
    | UInt64 => evalPowNat maxExponent getUInt64Value? (· ^ ·) a b
    | Int8 => evalPowNat maxExponent getInt8Value? (· ^ ·) a b
    | Int16 => evalPowNat maxExponent getInt16Value? (· ^ ·) a b
    | Int32 => evalPowNat maxExponent getInt32Value? (· ^ ·) a b
    | Int64 => evalPowNat maxExponent getInt64Value? (· ^ ·) a b
    | _ => return .rfl
  | Int => match_expr α with
    | Rat => evalPowInt maxExponent getRatValue? (· ^ ·) a b
    | _ => return .rfl
  | _ => return .rfl

abbrev shift [ShiftLeft α] [ShiftRight α] (left : Bool) (a b : α) : α :=
  if left then a <<< b else a >>> b

def evalShift (left : Bool) (α β : Expr) (a b : Expr) : DSimpM Result :=
  if isSameExpr α β then
    match_expr α with
    | Nat => evalBinNat (shift left) a b
    | Fin _ => if left then evalBinFin' (· <<< ·) a b else evalBinFin' (· >>> ·) a b
    | BitVec _ => if left then evalBinBitVec' (· <<< ·) a b else evalBinBitVec' (· >>> ·) a b
    | UInt8 => evalBinUInt8 (shift left) a b
    | UInt16 => evalBinUInt16 (shift left) a b
    | UInt32 => evalBinUInt32 (shift left) a b
    | UInt64 => evalBinUInt64 (shift left) a b
    | Int8 => evalBinInt8 (shift left) a b
    | Int16 => evalBinInt16 (shift left) a b
    | Int32 => evalBinInt32 (shift left) a b
    | Int64 => evalBinInt64 (shift left) a b
    | _ => return .rfl
  else
  match_expr β with
  | Nat =>
    match_expr α with
    | Int => do
      let some a := getIntValue? a | return .rfl
      let some b := getNatValue? b | return .rfl
      let e := if left then a <<< b else a >>> b
      let e ← share <| toExpr e
      return .step e (done := true)
    | BitVec _ => do
      let some a := getBitVecValue? a | return .rfl
      let some b := getNatValue? b | return .rfl
      let e := if left then a.val <<< b else a.val >>> b
      let e ← share <| toExpr e
      return .step e (done := true)
    | _ => return .rfl
  | BitVec _ => do
    let_expr BitVec _ := α | return .rfl
    let some a := getBitVecValue? a | return .rfl
    let some b := getBitVecValue? b | return .rfl
    let e := if left then a.val <<< b.val else a.val >>> b.val
    let e ← share <| toExpr e
    return .step e (done := true)
  | _ => return .rfl

def evalIntGcd (a b : Expr) : DSimpM Result := do
  let some a := getIntValue? a | return .rfl
  let some b := getIntValue? b | return .rfl
  let e ← share <| toExpr (Int.gcd a b)
  return .step e (done := true)

def evalIntBMod (a b : Expr) : DSimpM Result := do
  let some a := getIntValue? a | return .rfl
  let some b := getNatValue? b | return .rfl
  let e ← share <| toExpr (Int.bmod a b)
  return .step e (done := true)

def evalIntBDiv (a b : Expr) : DSimpM Result := do
  let some a := getIntValue? a | return .rfl
  let some b := getNatValue? b | return .rfl
  let e ← share <| toExpr (Int.bdiv a b)
  return .step e (done := true)

abbrev evalBinBoolPred (toValue? : Expr → Option α) (op : α → α → Bool) (a b : Expr) : DSimpM Result := do
  let some va := toValue? a | return .rfl
  let some vb := toValue? b | return .rfl
  let r := op va vb
  let e ← share (toExpr r)
  return .step e (done := true)

abbrev evalBinBoolPredNat : (op : Nat → Nat → Bool) → (a b : Expr) → DSimpM Result := evalBinBoolPred getNatValue?
abbrev evalBinBoolPredInt : (op : Int → Int → Bool) → (a b : Expr) → DSimpM Result := evalBinBoolPred getIntValue?
abbrev evalBinBoolPredRat : (op : Rat → Rat → Bool) → (a b : Expr) → DSimpM Result := evalBinBoolPred getRatValue?
abbrev evalBinBoolPredUInt8 : (op : UInt8 → UInt8 → Bool) → (a b : Expr) → DSimpM Result := evalBinBoolPred getUInt8Value?
abbrev evalBinBoolPredUInt16 : (op : UInt16 → UInt16 → Bool) → (a b : Expr) → DSimpM Result := evalBinBoolPred getUInt16Value?
abbrev evalBinBoolPredUInt32 : (op : UInt32 → UInt32 → Bool) → (a b : Expr) → DSimpM Result := evalBinBoolPred getUInt32Value?
abbrev evalBinBoolPredUInt64 : (op : UInt64 → UInt64 → Bool) → (a b : Expr) → DSimpM Result := evalBinBoolPred getUInt64Value?
abbrev evalBinBoolPredInt8 : (op : Int8 → Int8 → Bool) → (a b : Expr) → DSimpM Result := evalBinBoolPred getInt8Value?
abbrev evalBinBoolPredInt16 : (op : Int16 → Int16 → Bool) → (a b : Expr) → DSimpM Result := evalBinBoolPred getInt16Value?
abbrev evalBinBoolPredInt32 : (op : Int32 → Int32 → Bool) → (a b : Expr) → DSimpM Result := evalBinBoolPred getInt32Value?
abbrev evalBinBoolPredInt64 : (op : Int64 → Int64 → Bool) → (a b : Expr) → DSimpM Result := evalBinBoolPred getInt64Value?

abbrev evalBinBoolPredFin (op : {n : Nat} → Fin n → Fin n → Bool) (a b : Expr) : DSimpM Result := do
  let some a := getFinValue? a | return .rfl
  let some b := getFinValue? b | return .rfl
  if h : a.n = b.n then
    let r := op a.val (h ▸ b.val)
    let e ← share (toExpr r)
    return .step e (done := true)
  else
    return .rfl

abbrev evalBinBoolPredBitVec (op : {n : Nat} → BitVec n → BitVec n → Bool) (a b : Expr) : DSimpM Result := do
  let some a := getBitVecValue? a | return .rfl
  let some b := getBitVecValue? b | return .rfl
  if h : a.n = b.n then
    let r := op a.val (h ▸ b.val)
    let e ← share (toExpr r)
    return .step e (done := true)
  else
    return .rfl

macro "declare_eval_bin_bool_pred" id:ident op:term : command =>
  `(def $id:ident (α : Expr) (a b : Expr) : DSimpM Result :=
  match_expr α with
  | Nat => evalBinBoolPredNat $op a b
  | Int => evalBinBoolPredInt $op a b
  | Rat => evalBinBoolPredRat $op a b
  | Fin _ => evalBinBoolPredFin $op a b
  | BitVec _ => evalBinBoolPredBitVec $op a b
  | UInt8 => evalBinBoolPredUInt8 $op a b
  | UInt16 => evalBinBoolPredUInt16 $op a b
  | UInt32 => evalBinBoolPredUInt32 $op a b
  | UInt64 => evalBinBoolPredUInt64 $op a b
  | Int8 => evalBinBoolPredInt8 $op a b
  | Int16 => evalBinBoolPredInt16 $op a b
  | Int32 => evalBinBoolPredInt32 $op a b
  | Int64 => evalBinBoolPredInt64 $op a b
  | _ => return .rfl
  )

declare_eval_bin_bool_pred evalBEq (· == ·)
declare_eval_bin_bool_pred evalBNe (· != ·)

public structure EvalStepConfig where
  maxExponent := 255

/--
Simplification procedure that evaluates ground terms of builtin types.

**Important:** This procedure assumes subterms have already been simplified. It evaluates
a single operation on literal arguments only. For example:
- `2 + 3` → evaluates to `5`
- `2 + (3 * 4)` → returns `.rfl` (the argument `3 * 4` is not a literal)

The simplifier is responsible for term traversal, ensuring subterms are reduced
before `evalGround` is called on the parent expression.
-/
public def evalGround (config : EvalStepConfig := {}) : DSimproc := fun e =>
  match_expr e with
  | HAdd.hAdd α _ _ _ a b => evalAdd α a b
  | HSub.hSub α _ _ _ a b => evalSub α a b
  | HMul.hMul α _ _ _ a b => evalMul α a b
  | HDiv.hDiv α _ _ _ a b => evalDiv e α a b
  | HMod.hMod α _ _ _ a b => evalMod α a b
  | HPow.hPow α β _ _ a b => evalPow config.maxExponent α β a b
  | HAnd.hAnd α _ _ _ a b => evalAnd α a b
  | HXor.hXor α _ _ _ a b => evalXOr α a b
  | HOr.hOr α _ _ _ a b => evalOr α a b
  | HShiftLeft.hShiftLeft α β _ _ a b => evalShift (left := true) α β a b
  | HShiftRight.hShiftRight α β _ _ a b => evalShift (left := false) α β a b
  | Inv.inv α _ a => evalInv α a
  | Neg.neg α _ a => return skipIfUnchanged e (← evalNeg α a)
  | Complement.complement α _ a => evalComplement α a
  | Nat.gcd a b => evalBinNat Nat.gcd a b
  | Nat.succ a => evalUnaryNat (· + 1) a
  | Int.gcd a b => evalIntGcd a b
  | Int.tdiv a b => evalBinInt Int.tdiv a b
  | Int.fdiv a b => evalBinInt Int.fdiv a b
  | Int.bdiv a b => evalIntBDiv a b
  | Int.tmod a b => evalBinInt Int.tmod a b
  | Int.fmod a b => evalBinInt Int.fmod a b
  | Int.bmod a b => evalIntBMod a b
  | BEq.beq α _ a b => evalBEq α a b
  | bne α _ a b => evalBNe α a b
  | _  => return .rfl

end Lean.Meta.Sym.DSimp
