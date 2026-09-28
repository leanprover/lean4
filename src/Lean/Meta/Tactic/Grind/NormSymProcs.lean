/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Simp.SimpM
import Lean.Meta.Sym.Simp.Result
import Lean.Meta.Sym.AlphaShareBuilder
import Lean.Meta.Sym.InstantiateS
import Lean.Meta.Sym.InferType
import Lean.Meta.Sym.SynthInstance
import Lean.Meta.AppBuilder
import Lean.Meta.CtorRecognizer
import Init.Grind.Norm
import Init.Grind.Lemmas
import Init.ByCases
public section
namespace Lean.Meta.Grind.NormSym
open Sym.Simp (Simproc Result SimpM)
open Sym (getTrueExpr getFalseExpr getBoolTrueExpr getBoolFalseExpr share isSameExpr)
open Sym.Internal

/-!
# `Sym.simp` simprocs of the `grind` normalizer

Ports of the `Meta.simp` simprocs in `SimpUtil.lean` and `ForallProp.lean` whose rewrite rules
are not first-order (they bind variables or dispatch on the shape of the term). Results are
built with the maximal-sharing builders (`mkAppS`, ...); proofs are built without `inferType`.
The definitional reductions (beta, zeta, projections, matchers) are the shared ones in
`Lean.Meta.Sym.Simp.Reduce`.
-/

private def mkNotS (p : Expr) : SimpM Expr := do
  mkAppS (← mkConstS ``Not) p

private def mkAndS (p q : Expr) : SimpM Expr := do
  mkAppS₂ (← mkConstS ``And) p q

private def mkOrS (p q : Expr) : SimpM Expr := do
  mkAppS₂ (← mkConstS ``Or) p q

private def mkExistsS (u : Level) (α p : Expr) : SimpM Expr := do
  mkAppS₂ (← mkConstS ``Exists [u]) α p

/-- Erases metadata. `grind` never internalizes `Expr.mdata`. -/
def eraseMData : Simproc := fun e => do
  let .mdata _ b := e | return .rfl
  return .step b (← Sym.mkEqRefl b)

private def isBoolEqTarget (declName : Name) : Bool :=
  declName == ``Bool.and ||
  declName == ``Bool.or  ||
  declName == ``Bool.not ||
  declName == ``BEq.beq  ||
  declName == ``decide

/--
Normalizes equalities:
- `Bool`: `true = b` becomes `b = true`; `(a && b) = c` becomes `((a && b) = true) = (c = true)`.
- `a = a` becomes `True`, `p = True` becomes `p`, `p = False` becomes `¬p`.
-/
def simpEq : Simproc := fun e => do
  let_expr f@Eq α lhs rhs := e | return .rfl
  match_expr α with
  | Bool =>
    let .const rhsName _ := rhs.getAppFn | return .rfl
    if rhsName == ``true || rhsName == ``false then return .rfl
    let .const lhsName _ := lhs.getAppFn | return .rfl
    if lhsName == ``true || lhsName == ``false then
      return .step (← mkAppS₃ f α rhs lhs) (mkApp2 (mkConst ``Grind.flip_bool_eq) lhs rhs)
    if isBoolEqTarget lhsName || isBoolEqTarget rhsName then
      let tr ← getBoolTrueExpr
      -- `Bool : Type`, so `f` is `Eq.{1}`, which is also the equality of propositions.
      let e' ← mkAppS₃ f (← mkSortS .zero) (← mkAppS₃ f α lhs tr) (← mkAppS₃ f α rhs tr)
      return .step e' (mkApp2 (mkConst ``Grind.bool_eq_to_prop) lhs rhs)
    return .rfl
  | _ =>
    if isSameExpr lhs rhs then
      return .step (← getTrueExpr) (mkApp2 (mkConst ``eq_self f.constLevels!) α lhs) (done := true)
    else if rhs.isTrue then
      return .step lhs (mkApp (mkConst ``Grind.eq_true_eq) lhs) (done := true)
    else if rhs.isFalse then
      return .step (← mkNotS lhs) (mkApp (mkConst ``Grind.eq_false_eq) lhs)
    return .rfl

/-- Converts `dite` with non-dependent branches into `ite`. -/
def simpDIte : Simproc := fun e => do
  let_expr f@dite α c inst a b := e | return .rfl
  let .lam _ _ aBody _ := a | return .rfl
  if aBody.hasLooseBVars then return .rfl
  let .lam _ _ bBody _ := b | return .rfl
  if bBody.hasLooseBVars then return .rfl
  let us := f.constLevels!
  let e' ← mkAppS₅ (← mkConstS ``ite us) α c inst aBody bBody
  return .step e' (mkApp5 (mkConst ``dite_eq_ite us) c α aBody bBody inst)

/--
Pushes negations inwards through the propositional connectives, `ite`, and the quantifiers.
Negated arithmetic comparisons are handled by the rewrite rules `Nat.not_le_eq` and
`Int.not_le_eq`.
-/
def pushNot : Simproc := fun e => do
  let_expr Not p := e | return .rfl
  match_expr p with
  | True => return .step (← getFalseExpr) (mkConst ``Grind.not_true)
  | False => return .step (← getTrueExpr) (mkConst ``Grind.not_false)
  | And q r => return .step (← mkOrS (← mkNotS q) (← mkNotS r)) (mkApp2 (mkConst ``Grind.not_and) q r)
  | Or q r => return .step (← mkAndS (← mkNotS q) (← mkNotS r)) (mkApp2 (mkConst ``Grind.not_or) q r)
  | Not q => return .step q (mkApp (mkConst ``Grind.not_not) q)
  | f@Eq α a b =>
    if α.isProp then
      return .step (← mkAppS₃ f α a (← mkNotS b)) (mkApp2 (mkConst ``Grind.not_eq_prop) a b)
    else match_expr b with
      | Bool.true => return .step (← mkAppS₃ f α a (← getBoolFalseExpr)) (mkApp (mkConst ``Bool.not_eq_true) a)
      | Bool.false => return .step (← mkAppS₃ f α a (← getBoolTrueExpr)) (mkApp (mkConst ``Bool.not_eq_false) a)
      | _ => return .rfl
  | f@ite α c inst a b =>
    return .step (← mkAppS₅ f α c inst (← mkNotS a) (← mkNotS b)) (mkApp4 (mkConst ``Grind.not_ite) c inst a b)
  | Exists α q =>
    let e' ← mkForallS `a .default α (← mkNotS (← Sym.betaS q #[← mkBVarS 0]))
    let u ← Sym.getLevel α
    return .step e' (mkApp2 (mkConst ``Grind.not_exists [u]) α q)
  | _ =>
    let .forallE n α b info := p | return .rfl
    if !b.hasLooseBVars && (← isProp α) then
      return .step (← mkAndS α (← mkNotS b)) (mkApp2 (mkConst ``Grind.not_implies) α b)
    else
      let q    := mkLambda n info α b
      let notQ ← mkLambdaS n info α (← mkNotS b)
      let u ← Sym.getLevel α
      return .step (← mkExistsS u α notQ) (mkApp2 (mkConst ``Grind.not_forall [u]) α q)

/--
Normalizes disjunctions: units, right-associativity, and universally quantified disjuncts
moved to the front.
-/
def simpOr : Simproc := fun e => do
  let_expr Or p q := e | return .rfl
  match_expr p with
  | True => return .step p (mkApp (mkConst ``true_or) q)
  | False => return .step q (mkApp (mkConst ``false_or) q)
  | Or p₁ p₂ => return .step (← mkOrS p₁ (← mkOrS p₂ q)) (mkApp3 (mkConst ``Grind.or_assoc) p₁ p₂ q)
  | _ =>
  match_expr q with
  | Or q r =>
    if p.isForall then return .rfl
    if q.isForall then return .step (← mkOrS q (← mkOrS p r)) (mkApp3 (mkConst ``Grind.or_swap12) p q r)
    if r.isForall then return .step (← mkOrS r (← mkOrS q p)) (mkApp3 (mkConst ``Grind.or_swap13) p q r)
    return .rfl
  | True => return .step q (mkApp (mkConst ``or_true) p)
  | False => return .step p (mkApp (mkConst ``or_false) p)
  | _ => return .rfl

/-- Reduces `c₁ ... = c₂ ...` to `False` for distinct constructors `c₁` and `c₂`. -/
def reduceCtorEq : Simproc := fun e => do
  let_expr Eq _ lhs rhs := e | return .rfl
  let some c₁ ← isConstructorApp? lhs | return .rfl
  let some c₂ ← isConstructorApp? rhs | return .rfl
  if c₁.name == c₂.name then return .rfl
  let h ← withLocalDeclD `h e fun h => do
    withDefault <| mkEqFalse' (← mkLambdaFVars #[h] (← mkNoConfusion (mkConst ``False) h))
  return .step (← getFalseExpr) h (done := true)

private def isForallOrNot? (e : Expr) : Option (Name × Expr × Expr) :=
  if let .forallE n d b _ := e then
    some (n, d, b)
  else if e.isAppOfArity ``Not 1 then
    some (`a, e.appArg!, mkConst ``False)
  else
    none

/--
Normalizes universally quantified propositions and implications:
`Grind.imp_true_eq`, `Grind.imp_false_eq`, `Grind.forall_imp_eq_or`, `Grind.true_imp_eq`,
`Grind.false_imp_eq`, `Grind.imp_self_eq`, `Grind.forall_true`, `forall_false`,
`Grind.forall_or_forall`, `Grind.forall_forall_or`, `Grind.forall_and`.
-/
def simpForall : Simproc := fun e => do
  let .forallE varName d b info := e | return .rfl
  if !b.hasLooseBVars then
    match_expr d with
    | True => if (← isProp b) then return .step b (mkApp (mkConst ``Grind.true_imp_eq) b) (done := true)
    | False => if (← isProp b) then return .step (← getTrueExpr) (mkApp (mkConst ``Grind.false_imp_eq) b) (done := true)
    | _ =>
    if let .forallE aName α pRaw info' := d then
      if (← pure pRaw.hasLooseBVars <&&> isProp d) then
        let p := mkLambda aName info' α pRaw
        let q := b
        let u ← Sym.getLevel α
        let e' ← mkOrS (← mkExistsS u α (← mkLambdaS aName info' α (← mkNotS pRaw))) q
        return .step e' (mkApp3 (mkConst ``Grind.forall_imp_eq_or [u]) α p q)
    else match_expr b with
    | True => if (← isProp d) then return .step (← getTrueExpr) (mkApp (mkConst ``Grind.imp_true_eq) d) (done := true)
    | False => if (← isProp d) then return .step (← mkNotS d) (mkApp (mkConst ``Grind.imp_false_eq) d)
    | _ =>
      -- Maximally shared terms: structural equality is pointer equality.
      if isSameExpr d b && (← isProp d) then
        return .step (← getTrueExpr) (mkApp (mkConst ``Grind.imp_self_eq) d) (done := true)
  else
    match_expr d with
    | True =>
      let pTrue ← Sym.instantiateRevBetaS b #[← mkConstS ``True.intro]
      if (← isProp pTrue) then
        let p := mkLambda varName info d b
        return .step pTrue (mkApp (mkConst ``Grind.forall_true) p) (done := true)
    | False =>
      let p := mkLambda varName info d b
      if (← isDefEq (← inferType p) (mkForall varName info d (mkSort 0))) then
        return .step (← getTrueExpr) (mkApp (mkConst ``forall_false) p) (done := true)
    | _ => pure ()
  if b.isApp && b.getAppNumArgs == 2 then
    let .const bDeclName _ := b.appFn!.appFn! | return .rfl
    if bDeclName == ``Or then
      let left  := b.appFn!.appArg!
      let right := b.appArg!
      let α := d
      if let some (bName, βRaw, qRaw) := isForallOrNot? left then
        let pRaw := right
        let p := mkLambda varName info α pRaw
        let q := mkLambda varName info α (mkLambda bName .default βRaw qRaw)
        let β := mkLambda varName info α βRaw
        let u ← Sym.getLevel α
        let v ← withLocalDeclD varName α fun a => Meta.getLevel (βRaw.instantiate1 a)
        let body ← mkOrS qRaw (← share (pRaw.liftLooseBVars 0 1))
        let e' ← mkForallS varName info α (← mkForallS bName .default βRaw body)
        return .step e' (mkApp4 (mkConst ``Grind.forall_forall_or [u, v]) α β p q)
      else if let some (bName, βRaw, qRaw) := isForallOrNot? right then
        let pRaw := left
        let p := mkLambda varName info α pRaw
        let q := mkLambda varName info α (mkLambda bName .default βRaw qRaw)
        let β := mkLambda varName info α βRaw
        let u ← Sym.getLevel α
        let v ← withLocalDeclD varName α fun a => Meta.getLevel (βRaw.instantiate1 a)
        let body ← mkOrS (← share (pRaw.liftLooseBVars 0 1)) qRaw
        let e' ← mkForallS varName info α (← mkForallS bName .default βRaw body)
        return .step e' (mkApp4 (mkConst ``Grind.forall_or_forall [u, v]) α β p q)
    else if bDeclName == ``And then
      let pRaw := b.appFn!.appArg!
      let qRaw := b.appArg!
      let p := mkLambda varName info d pRaw
      let q := mkLambda varName info d qRaw
      let e' ← mkAndS (← mkForallS varName info d pRaw) (← mkForallS varName info d qRaw)
      let u ← Sym.getLevel d
      return .step e' (mkApp3 (mkConst ``Grind.forall_and [u]) d p q)
  return .rfl

/--
Normalizes existentially quantified propositions:
`Grind.exists_or`, `Grind.exists_and_left`, `Grind.exists_and_right`, `Grind.exists_prop`,
`Grind.exists_const`.
-/
def simpExists : Simproc := fun e => do
  let_expr ex@Exists α fn := e | return .rfl
  let .lam x _ b _ := fn | return .rfl
  let u := ex.constLevels!
  if b.isApp && b.getAppNumArgs == 2 then
    let .const bDeclName _ := b.appFn!.appFn! | return .rfl
    if bDeclName == ``Or then
      let pRaw := b.appFn!.appArg!
      let qRaw := b.appArg!
      let p ← mkLambdaS x .default α pRaw
      let q ← mkLambdaS x .default α qRaw
      let e' ← mkOrS (← mkAppS₂ ex α p) (← mkAppS₂ ex α q)
      return .step e' (mkApp3 (mkConst ``Grind.exists_or u) α p q)
    else if bDeclName == ``And then
      let pRaw := b.appFn!.appArg!
      let qRaw := b.appArg!
      if !pRaw.hasLooseBVars then
        let b := pRaw
        let p ← mkLambdaS x .default α qRaw
        let e' ← mkAndS b (← mkAppS₂ ex α p)
        return .step e' (mkApp3 (mkConst ``Grind.exists_and_left u) α p b)
      else if !qRaw.hasLooseBVars then
        let p ← mkLambdaS x .default α pRaw
        let b := qRaw
        let e' ← mkAndS (← mkAppS₂ ex α p) b
        return .step e' (mkApp3 (mkConst ``Grind.exists_and_right u) α p b)
  if !b.hasLooseBVars then
    if (← isProp α) then
      return .step (← mkAndS α b) (mkApp2 (mkConst ``Grind.exists_prop) α b)
    else
      let nonempty ← mkAppS (← mkConstS ``Nonempty u) α
      if let some nonemptyInst ← Sym.synthInstance? nonempty then
        return .step b (mkApp3 (mkConst ``Grind.exists_const u) α nonemptyInst b)
  return .rfl

end Lean.Meta.Grind.NormSym
