/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module
prelude
public import Lean.Meta.Sym.Simp.SimpM
import Lean.Meta.Sym.Util
import Lean.Meta.Sym.InstantiateS
import Lean.Meta.Sym.InferType
import Init.Grind.Norm
import Init.Sym.Lemmas
import Lean.Meta.AppBuilder

/-!
This module provides simplification procedures for turning propositional formulas into negation
normal form (NNF), i.e. pushing in all negation as far as possible.
-/

namespace Lean.Meta.Sym.Simp

open Sym.Internal

public def nnf : Simproc := fun e => do
  match_expr e with
  | Not p =>
    match_expr p with
    | True => return .step (← getFalseExpr) (mkConst ``Grind.not_true)
    | False => return .step (← getTrueExpr) (mkConst ``Grind.not_false)
    | And q r => return .step (← mkOrS (← mkNotS q) (← mkNotS r)) (mkApp2 (mkConst ``Grind.not_and) q r)
    | Or q r => return .step (← mkAndS (← mkNotS q) (← mkNotS r)) (mkApp2 (mkConst ``Grind.not_or) q r)
    | Not q => return .step q (mkApp (mkConst ``Grind.not_not) q)
    | Exists α q =>
      let e' ← mkForallS `a .default α (← mkNotS (← betaS q #[← mkBVarS 0]))
      let u ← Sym.getLevel α
      return .step e' (mkApp2 (mkConst ``Grind.not_exists [u]) α q)
    | Eq α a b =>
      unless α.isConstOf ``Bool do return .rfl
      match boolLit? b, boolLit? a with
      | some true, _ => return .step (← mkBoolEqS a false) (mkApp (mkConst ``Bool.not_eq_true) a)
      | some false, _ => return .step (← mkBoolEqS a true) (mkApp (mkConst ``Bool.not_eq_false) a)
      | none, some _ =>
        let h := boolEqComm a b
        let p' ← mkEqS b a
        let expr ← mkNotS <| p'
        let proof := mkApp6 (mkConst ``congrArg [1, 1]) (.sort 0) (.sort 0) p p' (mkConst ``Not) h
        return .step expr proof
      | none, none => return .rfl
    | _ =>
      let .forallE n α b info := p | return .rfl
      if ← pure !b.hasLooseBVars <&&> isProp α then return .rfl -- it's an implication
      let q := mkLambda n info α b
      let notQ ← mkLambdaS n info α (← mkNotS b)
      let u ← Sym.getLevel α
      return .step (← mkExistsS u α notQ) (mkApp2 (mkConst ``Grind.not_forall [u]) α q)
  | Eq α a b =>
    if α.isConstOf ``Bool then return ← boolEq a b
    unless α.isProp do return .rfl
    let expr ← mkAndS (← mkArrowS a b) (← mkArrowS b a)
    let proof := mkApp2 (mkConst ``Sym.eq_prop_eq_and) a b
    return .step expr proof
  | Iff a b =>
    let expr ← mkAndS (← mkArrowS a b) (← mkArrowS b a)
    let proof := mkApp2 (mkConst ``Lean.Sym.iff_eq_and) a b
    return .step expr proof
  | ite α c inst a b =>
    unless α.isProp do return .rfl
    let expr ← mkAndS (← mkArrowS c a) (← mkArrowS (← mkNotS c) b)
    let proof := mkApp4 (mkConst ``Lean.Sym.ite_eq_and) c inst a b
    return .step expr proof
  | cond α c a b =>
    unless α.isProp do return .rfl
    let cProp ← mkAppS₃ (← mkConstS ``Eq [1]) (← mkConstS ``Bool) c (← getBoolTrueExpr)
    let expr ← mkAndS (← mkArrowS cProp a) (← mkArrowS (← mkNotS cProp) b)
    let proof := mkApp3 (mkConst ``Lean.Sym.cond_eq_and) c a b
    return .step expr proof
  | _ =>
    let .forallE _ α b _ := e | return .rfl
    unless ← pure (!b.hasLooseBVars) <&&> isProp α <&&> isProp b do return .rfl
    return .step (← mkOrS (← mkNotS α) b) (mkApp2 (mkConst ``Lean.Sym.imp_eq) α b)
where
  mkArrowS (p q : Expr) : SymM Expr := mkForallS .anonymous .default p q

  boolLit? (e : Expr) : Option Bool :=
    if e.isConstOf ``Bool.true then
      some true
    else if e.isConstOf ``Bool.false then
      some false
    else
      none

  mkEqS (a b : Expr) : SymM Expr := do
    mkAppS₃ (← mkConstS ``Eq [1]) (← mkConstS ``Bool) a b

  mkBoolEqS (a : Expr) (b : Bool) : SymM Expr := do
    mkEqS a (← if b then getBoolTrueExpr else getBoolFalseExpr)

  /-- A proof of `(a = b) = (b = a)` for `a b : Bool`. -/
  boolEqComm (a b : Expr) : Expr :=
    let bool := mkConst ``Bool
    mkApp3 (mkConst ``propext) (mkApp3 (mkConst ``Eq [1]) bool a b) (mkApp3 (mkConst ``Eq [1]) bool b a) (mkApp3 (mkConst ``eq_comm [1]) bool a b)

  /-- Turn the `Bool` connectives of `a = t` into `Prop` ones, where `t` is a literal. -/
  boolEq (a t : Expr) : SymM Result := do
    if let some tv := boolLit? t then
      let lhs := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) a t
      let ofIff (rhs h : Expr) : Expr := mkApp3 (mkConst ``propext) lhs rhs h
      match_expr a with
      | Bool.not x =>
        let thm := if tv then ``Bool.not_eq_true' else ``Bool.not_eq_false'
        let expr ← mkBoolEqS x !tv
        let proof := mkApp (mkConst thm) x
        return .step expr proof
      | Bool.and x y =>
        if tv then
          let expr ← mkAndS (← mkBoolEqS x true) (← mkBoolEqS y true)
          let proof := mkApp2 (mkConst ``Bool.and_eq_true) x y
          return .step expr proof
        else
          let expr ← mkOrS (← mkBoolEqS x false) (← mkBoolEqS y false)
          let proof := ofIff expr (mkApp2 (mkConst ``Bool.and_eq_false_iff) x y)
          return .step expr proof
      | Bool.or x y =>
        if tv then
          let expr ← mkOrS (← mkBoolEqS x true) (← mkBoolEqS y true)
          let proof := mkApp2 (mkConst ``Bool.or_eq_true) x y
          return .step expr proof
        else
          let expr ← mkAndS (← mkBoolEqS x false) (← mkBoolEqS y false)
          let proof := ofIff expr (mkApp2 (mkConst ``Bool.or_eq_false_iff) x y)
          return .step expr proof
      -- `Bool.xor` is not present in Sym code as it is reducible
      -- | Bool.xor x y =>
      | bne α _ x y =>
        unless α.isConstOf ``Bool do return .rfl
        if tv then
          let expr ← mkNotS (← mkEqS x y)
          let proof := ofIff expr (← mkAppOptM ``bne_iff_ne #[α, none, none, x, y])
          return .step expr proof
        else
          let expr ← mkEqS x y
          let proof := ofIff expr (← mkAppOptM ``bne_eq_false_iff_eq #[α, none, none, x, y])
          return .step expr proof
      | BEq.beq α _ x y =>
        unless α.isConstOf ``Bool do return .rfl
        if tv then
          let expr ← mkEqS x y
          let proof := mkApp2 (mkConst ``Bool.beq_to_eq) x y
          return .step expr proof
        else
          let expr ← mkNotS (← mkEqS x y)
          let proof := ofIff expr (← mkAppOptM ``beq_eq_false_iff_ne #[α, none, none, x, y])
          return .step expr proof
      | decide p inst =>
        if tv then
          let proof := mkApp2 (mkConst ``decide_eq_true_eq) p inst
          return .step p proof
        else
          let expr ← mkNotS p
          let proof := ofIff expr (mkApp2 (mkConst ``decide_eq_false_iff_not) p inst)
          return .step expr proof
      | cond _ c x y =>
        let expr ← mkAndS (← mkOrS (← mkBoolEqS c false) (← mkEqS x t)) (← mkOrS (← mkBoolEqS c true) (← mkEqS y t))
        let proof := mkApp4 (mkConst ``Lean.Sym.cond_bool_eq) c x y t
        return .step expr proof
      | ite _ c inst x y =>
        let expr ← mkAndS (← mkOrS (← mkNotS c) (← mkEqS x t)) (← mkOrS c (← mkEqS y t))
        let proof := mkApp5 (mkConst ``Lean.Sym.ite_bool_eq) c inst x y t
        return .step expr proof
      | _ => return .rfl
    else
      if (boolLit? a).isSome then
        return .step (← mkEqS t a) (boolEqComm a t)
      else
        return .rfl


end Lean.Meta.Sym.Simp
