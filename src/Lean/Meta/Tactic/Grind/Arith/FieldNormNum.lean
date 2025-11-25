/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Basic
import Lean.Meta.Tactic.Grind.SynthInstance
import Lean.Util.SafeExponentiation
import Lean.Meta.AppBuilder
import Init.Grind.FieldNormNum
namespace Lean.Meta.Grind.Arith
namespace FieldNormNum

structure Context where
  u : Level
  type : Expr
  fieldInst : Expr
  ringInst : Expr
  semiringInst : Expr

abbrev M := OptionT <| ReaderT Context MetaM

def run? (type : Expr) (x : M α) : MetaM (Option α) := do
  let some u ← getDecLevel? type | return none
  let some fieldInst ← synthInstanceMeta? (mkApp (mkConst ``Grind.Field [u]) type) | return none
  let commRingInst := mkApp2 (mkConst ``Grind.Field.toCommRing [u]) type fieldInst
  let ringInst := mkApp2 (mkConst ``Grind.CommRing.toRing [u]) type commRingInst
  let semiringInst := mkApp2 (mkConst ``Grind.Ring.toSemiring [u]) type ringInst
  x.run { u, type, fieldInst, ringInst, semiringInst }

def isAddInst (inst : Expr) : M Bool := do
  let ctx ← read
  let expectedInst := mkApp2 (mkConst ``instHAdd [ctx.u]) ctx.type <| mkApp2 (mkConst ``Grind.Semiring.toAdd [ctx.u]) ctx.type ctx.semiringInst
  isDefEqI inst expectedInst

def isMulInst (inst : Expr) : M Bool := do
  let ctx ← read
  let expectedInst := mkApp2 (mkConst ``instHMul [ctx.u]) ctx.type <| mkApp2 (mkConst ``Grind.Semiring.toMul [ctx.u]) ctx.type ctx.semiringInst
  isDefEqI inst expectedInst

def isSubInst (inst : Expr) : M Bool := do
  let ctx ← read
  let expectedInst := mkApp2 (mkConst ``instHSub [ctx.u]) ctx.type <| mkApp2 (mkConst ``Grind.Ring.toSub [ctx.u]) ctx.type ctx.ringInst
  isDefEqI inst expectedInst

def isDivInst (inst : Expr) : M Bool := do
  let ctx ← read
  let expectedInst := mkApp2 (mkConst ``instHDiv [ctx.u]) ctx.type <| mkApp2 (mkConst ``Grind.Field.toDiv [ctx.u]) ctx.type ctx.fieldInst
  isDefEqI inst expectedInst

def isNegInst (inst : Expr) : M Bool := do
  let ctx ← read
  let expectedInst := mkApp2 (mkConst ``Grind.Ring.toNeg [ctx.u]) ctx.type ctx.ringInst
  isDefEqI inst expectedInst

def isInvInst (inst : Expr) : M Bool := do
  let ctx ← read
  let expectedInst := mkApp2 (mkConst ``Grind.Field.toInv [ctx.u]) ctx.type ctx.fieldInst
  isDefEqI inst expectedInst

def isNPowInst (inst : Expr) : M Bool := do
  let ctx ← read
  let expectedInst := mkApp2 (mkConst ``Grind.Semiring.npow [ctx.u]) ctx.type ctx.semiringInst
  isDefEqI inst expectedInst

def isZPowInst (inst : Expr) : M Bool := do
  let ctx ← read
  let expectedInst := mkApp2 (mkConst ``Grind.Field.zpow [ctx.u]) ctx.type ctx.fieldInst
  isDefEqI inst expectedInst

def isOfNatInst (inst : Expr) (n : Expr) : M Bool := do
  let ctx ← read
  let expectedInst := mkApp3 (mkConst ``Grind.Semiring.ofNat [ctx.u]) ctx.type ctx.semiringInst n
  isDefEqI inst expectedInst

def isNatCastInst (inst : Expr) : M Bool := do
  let ctx ← read
  let expectedInst := mkApp2 (mkConst ``Grind.Semiring.natCast [ctx.u]) ctx.type ctx.semiringInst
  isDefEqI inst expectedInst

def isIntCastInst (inst : Expr) : M Bool := do
  let ctx ← read
  let expectedInst := mkApp2 (mkConst ``Grind.Ring.intCast [ctx.u]) ctx.type ctx.ringInst
  isDefEqI inst expectedInst

def mkBin (declName : Name) (a b : Expr) (r₁ r₂ : Rat × Expr) (op : Rat → Rat → Rat) : M (Rat × Expr) := do
  let ctx ← read
  let (v₁, h₁) := r₁
  let (v₂, h₂) := r₂
  let v := op v₁ v₂
  let h := mkApp10 (mkConst declName [ctx.u]) ctx.type ctx.fieldInst a b (toExpr v₁) (toExpr v₂) (toExpr v) eagerReflBoolTrue h₁ h₂
  return (v, h)

def mkUnary (declName : Name) (a : Expr) (r : Rat × Expr) (op : Rat → Rat) : M (Rat × Expr) := do
  let ctx ← read
  let (v₁, h₁) := r
  let v := op v₁
  let h := mkApp7 (mkConst declName [ctx.u]) ctx.type ctx.fieldInst a (toExpr v₁) (toExpr v) eagerReflBoolTrue h₁
  return (v, h)

partial def eval (e : Expr) : M (Rat × Expr) := do
  match_expr e with
  | HAdd.hAdd _ _ _ inst a b =>
    guard (← isAddInst inst)
    mkBin ``Grind.Field.NormNum.add_eq a b (← eval a) (← eval b) (· + ·)
  | HMul.hMul _ _ _ inst a b =>
    guard (← isMulInst inst)
    mkBin ``Grind.Field.NormNum.mul_eq a b (← eval a) (← eval b) (· * ·)
  | HSub.hSub _ _ _ inst a b =>
    guard (← isSubInst inst)
    mkBin ``Grind.Field.NormNum.sub_eq a b (← eval a) (← eval b) (· - ·)
  | HDiv.hDiv _ _ _ inst a b =>
    guard (← isDivInst inst)
    mkBin ``Grind.Field.NormNum.div_eq a b (← eval a) (← eval b) (· / ·)
  | Neg.neg _ inst a =>
    guard (← isNegInst inst)
    mkUnary ``Grind.Field.NormNum.neg_eq a (← eval a) (- ·)
  | Inv.inv _ inst a =>
    guard (← isInvInst inst)
    mkUnary ``Grind.Field.NormNum.inv_eq a (← eval a) (·⁻¹)
  | OfNat.ofNat _ n inst =>
    guard (← isOfNatInst inst n)
    let some v ← getNatValue? n | failure
    let ctx ← read
    let h := mkApp3 (mkConst ``Grind.Field.NormNum.ofNat_eq [ctx.u]) ctx.type ctx.fieldInst (toExpr v)
    return ((v : Rat), h)
  | NatCast.natCast _ inst n =>
    guard (← isNatCastInst inst)
    let some v ← getNatValue? n | failure
    let ctx ← read
    let h := mkApp3 (mkConst ``Grind.Field.NormNum.natCast_eq [ctx.u]) ctx.type ctx.fieldInst (toExpr v)
    return ((v : Rat), h)
  | IntCast.intCast _ inst n =>
    guard (← isIntCastInst inst)
    let some v ← getIntValue? n | failure
    let ctx ← read
    let h := mkApp3 (mkConst ``Grind.Field.NormNum.intCast_eq [ctx.u]) ctx.type ctx.fieldInst (toExpr v)
    return ((v : Rat), h)
  | HPow.hPow _ _ _ inst a b =>
    if (← isNPowInst inst) then
      let (v₁, h₁) ← eval a
      let some n ← getNatValue? b | failure
      let ctx ← read
      -- **Note**: Would be great to be able to use `Grind.Config.exp`, but we don't have access to it in the `MetaM` monad
      guard (← checkExponent n (warning := false))
      let v := v₁ ^ n
      let h := mkApp8 (mkConst ``Grind.Field.NormNum.npow_eq [ctx.u]) ctx.type ctx.fieldInst a (toExpr n) (toExpr v₁) (toExpr v) eagerReflBoolTrue h₁
      return (v, h)
    else if (← isZPowInst inst) then
      let (v₁, h₁) ← eval a
      let some n ← getIntValue? b | failure
      let ctx ← read
      guard (← checkExponent n.natAbs (warning := false))
      let v := v₁ ^ n
      let h := mkApp8 (mkConst ``Grind.Field.NormNum.zpow_eq [ctx.u]) ctx.type ctx.fieldInst a (toExpr n) (toExpr v₁) (toExpr v) eagerReflBoolTrue h₁
      return (v, h)
    else
      failure
  | _ => failure

end FieldNormNum

/--
Evaluates the `Field` expression `e` with type `type` using the given exponential threshold,
and returns `some (v, h)` s.t. `h : e = ofRat v` if successful.
-/
public def evalFieldExpr? (e : Expr) (type : Expr) : MetaM (Option (Rat × Expr)) := do
  FieldNormNum.run? type <| FieldNormNum.eval e

public def normFieldExpr? (e : Expr) (type : Expr) : MetaM (Option (Expr × Expr)) := do
  FieldNormNum.run? type do
    let (v, h) ← FieldNormNum.eval e
    let ctx ← read
    if v.den == 1 then
      let r ← mkAppOptM ``IntCast.intCast #[type, none, mkIntLit v.num]
      let h := mkApp7 (mkConst ``Grind.Field.NormNum.eq_int [ctx.u]) ctx.type ctx.fieldInst e (toExpr v) (toExpr v.num) eagerReflBoolTrue h
      return (r, h)
    else if v.num == 1 then
      let r ← mkAppOptM ``NatCast.natCast #[type, none, mkNatLit v.den]
      let r ← mkAppM ``Inv.inv #[r]
      let h := mkApp7 (mkConst ``Grind.Field.NormNum.eq_inv [ctx.u]) ctx.type ctx.fieldInst e (toExpr v) (toExpr v.den) eagerReflBoolTrue h
      return (r, h)
    else
      let n ← mkAppOptM ``IntCast.intCast #[type, none, mkIntLit v.num]
      let d ← mkAppOptM ``NatCast.natCast #[type, none, mkNatLit v.den]
      let d ← mkAppM ``Inv.inv #[d]
      let r ← mkMul n d
      let h := mkApp8 (mkConst ``Grind.Field.NormNum.eq_mul_inv [ctx.u]) ctx.type ctx.fieldInst e (toExpr v) (toExpr v.num) (toExpr v.den) eagerReflBoolTrue h
      return (r, h)

end Lean.Meta.Grind.Arith
