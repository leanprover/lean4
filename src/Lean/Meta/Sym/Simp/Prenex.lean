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
import Lean.Meta.Sym.SynthInstance
import Init.Sym.Lemmas

/-!
This module provides simplification procedures for turning propositional formulas into
prenex normal form, i.e. pulling out all quantifiers to the front. To avoid the
creation of skolem functions, it additionally provides support for minscoping. The simprocs all
assume that the formula has already been turned into NNF.
-/

namespace Lean.Meta.Sym.Simp

open Sym.Internal

def synthNonempty? (α : Expr) : SymM (Option Expr) := do
  let lvl ← getLevel α
  synthInstance? (← mkAppS (← mkConstS ``Nonempty [lvl]) α)

def mkPropEqSymm (lhs rhs h : Expr) : Expr :=
  mkApp4 (mkConst ``Eq.symm [1]) (mkSort 0) rhs lhs h

public def minscope : Simproc := fun e => do
  match_expr e with
  | Exists _ q =>
    let .lam n α b info := q | return .rfl
    let lvl ← Sym.getLevel α
    let mkEx (p : Expr) : SymM Expr := do mkExistsS lvl α (← mkLambdaS n info α p)
    match_expr b with
    | And p r =>
      if !r.hasLooseBVars then
        let pEx ← mkEx p
        let expr ← mkAndS pEx r
        let h := mkApp3 (mkConst ``Sym.exists_and_eq [lvl]) α pEx.appArg! r
        return .step expr (mkPropEqSymm e expr h)
      else if !p.hasLooseBVars then
        let rEx ← mkEx r
        let expr ← mkAndS p rEx
        let h := mkApp3 (mkConst ``Lean.Sym.and_exists_eq [lvl]) α p rEx.appArg!
        return .step expr (mkPropEqSymm e expr h)
      else
        return .rfl
    | Or p r =>
      -- With `Nonempty α`, keep the independent side out of the binder instead of distributing.
      if !r.hasLooseBVars || !p.hasLooseBVars then
        if let some inst ← synthNonempty? α then
          if !r.hasLooseBVars then
            let pEx ← mkEx p
            let expr ← mkOrS pEx r
            let h := mkApp4 (mkConst ``Lean.Sym.exists_or_eq [lvl]) α inst pEx.appArg! r
            return .step expr (mkPropEqSymm e expr h)
          else
            let rEx ← mkEx r
            let expr ← mkOrS p rEx
            let h := mkApp4 (mkConst ``Lean.Sym.or_exists_eq [lvl]) α inst p rEx.appArg!
            return .step expr (mkPropEqSymm e expr h)
      let pEx ← mkEx p
      let rEx ← mkEx r
      let expr ← mkOrS pEx rEx
      let h := mkApp3 (mkConst ``Lean.Sym.exists_or_exists_eq [lvl]) α pEx.appArg! rEx.appArg!
      return .step expr (mkPropEqSymm e expr h)
    | _ => return .rfl
  | _ =>
    let .forallE n α b info := e | return .rfl
    unless b.hasLooseBVars do return .rfl
    let lvl ← Sym.getLevel α
    match_expr b with
    | And p r =>
      if !r.hasLooseBVars || !p.hasLooseBVars then
        if let some inst ← synthNonempty? α then
          if !r.hasLooseBVars then
            let expr ← mkAndS (← mkForallS n info α p) r
            let h := mkApp4 (mkConst ``Lean.Sym.forall_and_eq [lvl]) α inst (mkLambda n info α p) r
            return .step expr (mkPropEqSymm e expr h)
          else
            let expr ← mkAndS p (← mkForallS n info α r)
            let h := mkApp4 (mkConst ``Lean.Sym.and_forall_eq [lvl]) α inst p (mkLambda n info α r)
            return .step expr (mkPropEqSymm e expr h)
        -- Distributing would turn the independent side into an implication, breaking NNF.
        if (← isProp α) then return .rfl
      let expr ← mkAndS (← mkForallS n info α p) (← mkForallS n info α r)
      let h := mkApp3 (mkConst ``Lean.Sym.forall_and_forall_eq [lvl]) α
        (mkLambda n info α p) (mkLambda n info α r)
      return .step expr (mkPropEqSymm e expr h)
    | Or p r =>
      if !r.hasLooseBVars then
        let expr ← mkOrS (← mkForallS n info α p) r
        let h := mkApp3 (mkConst ``Lean.Sym.forall_or_eq [lvl]) α (mkLambda n info α p) r
        return .step expr (mkPropEqSymm e expr h)
      else if !p.hasLooseBVars then
        let expr ← mkOrS p (← mkForallS n info α r)
        let h := mkApp3 (mkConst ``Lean.Sym.or_forall_eq [lvl]) α p (mkLambda n info α r)
        return .step expr (mkPropEqSymm e expr h)
      else
        return .rfl
    | _ => return .rfl

public def pullExists : Simproc := fun e => do
  match_expr e with
  | And q r =>
    if let some (α, b) ← matchExists? q then
      let lvl ← Sym.getLevel α
      let expr ← mkExistsS lvl α (← mkLambdaS .anonymous .default α (← mkAndS (← beta0 b) r))
      let proof := mkApp3 (mkConst ``Lean.Sym.exists_and_eq [lvl]) α b r
      return .step expr proof
    else if let some (α, b) ← matchExists? r then
      let lvl ← Sym.getLevel α
      let expr ← mkExistsS lvl α (← mkLambdaS .anonymous .default α (← mkAndS q (← beta0 b)))
      let proof := mkApp3 (mkConst ``Lean.Sym.and_exists_eq [lvl]) α q b
      return .step expr proof
    else
      return .rfl
  | Or q r =>
    let tryLeft (qα qb : Expr) : SymM Simp.Result := do
      let some qαNonempty ← synthNonempty? qα | return .rfl
      let lvl ← Sym.getLevel qα
      let expr ← mkExistsS lvl qα (← mkLambdaS .anonymous .default qα (← mkOrS (← beta0 qb) r))
      let proof := mkApp4 (mkConst ``Lean.Sym.exists_or_eq [lvl]) qα qαNonempty qb r
      return .step expr proof
    let tryRight (rα rb : Expr) : SymM Simp.Result := do
      let some rαNonempty ← synthNonempty? rα | return .rfl
      let lvl ← Sym.getLevel rα
      let expr ← mkExistsS lvl rα (← mkLambdaS .anonymous .default rα (← mkOrS q (← beta0 rb)))
      let proof := mkApp4 (mkConst ``Lean.Sym.or_exists_eq [lvl]) rα rαNonempty q rb
      return .step expr proof
    match ← matchExists? q, ← matchExists? r with
    | some (qα, qb), some (rα, rb) =>
      if qα != rα then
        match ← tryLeft qα qb with
        | ret@(.step ..) => return ret
        | .rfl .. => return ← tryRight rα rb
      let lvl ← Sym.getLevel qα
      let expr ← mkExistsS lvl qα (← mkLambdaS .anonymous .default qα (← mkOrS (← beta0 qb) (← beta0 rb)))
      let proof := mkApp3 (mkConst ``Lean.Sym.exists_or_exists_eq [lvl]) qα qb rb
      return .step expr proof
    | some (qα, qb), none =>
      tryLeft qα qb
    | none, some (rα, rb) =>
      tryRight rα rb
    | none, none => return .rfl
  | _ => return .rfl
where
  beta0 (e : Expr) : SymM Expr := do
    betaS e #[← mkBVarS 0]

  matchExists? (e : Expr) : SymM (Option (Expr × Expr)) := do
    let_expr Exists α q := e | return none
    return some (α, q)

public def pullForall : Simproc := fun e => do
  match_expr e with
  | And q r =>
    let tryLeft (qn : Name) (qα qb : Expr) (qinfo : BinderInfo) : SymM Simp.Result := do
      let some qαNonempty ← synthNonempty? qα | return .rfl
      let lvl ← Sym.getLevel qα
      let qlam := mkLambda qn qinfo qα qb
      let expr ← mkForallS qn qinfo qα (← mkAndS qb r)
      let proof := mkApp4 (mkConst ``Lean.Sym.forall_and_eq [lvl]) qα qαNonempty qlam r
      return .step expr proof
    let tryRight (rn : Name) (rα rb : Expr) (rinfo : BinderInfo) : SymM Simp.Result := do
      let some rαNonempty ← synthNonempty? rα | return .rfl
      let lvl ← Sym.getLevel rα
      let rlam := mkLambda rn rinfo rα rb
      let expr ← mkForallS rn rinfo rα (← mkAndS q rb)
      let proof := mkApp4 (mkConst ``Lean.Sym.and_forall_eq [lvl]) rα rαNonempty q rlam
      return .step expr proof
    match ← matchForall? q, ← matchForall? r with
    | some (qn, qα, qb, qinfo), some (rn, rα, rb, rinfo) =>
      if qα != rα then
        match ← tryLeft qn qα qb qinfo with
        | ret@(.step ..) => return ret
        | .rfl .. => return ← tryRight rn rα rb rinfo
      let lvl ← Sym.getLevel qα
      let qlam := mkLambda qn qinfo qα qb
      let rlam := mkLambda rn rinfo rα rb
      let expr ← mkForallS qn qinfo qα (← mkAndS qb rb)
      let proof := mkApp3 (mkConst ``Lean.Sym.forall_and_forall_eq [lvl]) qα qlam rlam
      return .step expr proof
    | some (qn, qα, qb, qinfo), none =>
      tryLeft qn qα qb qinfo
    | none, some (rn, rα, rb, rinfo) =>
      tryRight rn rα rb rinfo
    | none, none => return .rfl
  | Or q r =>
    if let some (qn, qα, qb, qinfo) ← matchForall? q then
      let lvl ← Sym.getLevel qα
      let qlam := mkLambda qn qinfo qα qb
      let expr ← mkForallS qn qinfo qα (← mkOrS qb r)
      let proof := mkApp3 (mkConst ``Lean.Sym.forall_or_eq [lvl]) qα qlam r
      return .step expr proof
    else if let some (rn, rα, rb, rinfo) ← matchForall? r then
      let lvl ← Sym.getLevel rα
      let rlam := mkLambda rn rinfo rα rb
      let expr ← mkForallS rn rinfo rα (← mkOrS q rb)
      let proof := mkApp3 (mkConst ``Lean.Sym.or_forall_eq [lvl]) rα q rlam
      return .step expr proof
    else
      return .rfl
  | _ => return .rfl
where
  matchForall? (e : Expr) : SymM (Option (Name × Expr × Expr × BinderInfo)) := do
    let .forallE n α b info := e | return none
    if !b.hasLooseBVars && (← isProp α) then return none
    return some (n, α, b, info)

end Lean.Meta.Sym.Simp
