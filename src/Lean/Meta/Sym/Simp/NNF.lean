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
    | _ =>
      let .forallE n α b info := p | return .rfl
      if ← pure !b.hasLooseBVars <&&> isProp α then return .rfl -- it's an implication
      let q := mkLambda n info α b
      let notQ ← mkLambdaS n info α (← mkNotS b)
      let u ← Sym.getLevel α
      return .step (← mkExistsS u α notQ) (mkApp2 (mkConst ``Grind.not_forall [u]) α q)
  | Eq α a b =>
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


end Lean.Meta.Sym.Simp
