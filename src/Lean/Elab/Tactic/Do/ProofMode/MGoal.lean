/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Sebastian Graf
-/
module

prelude
public import Std.Do.SPred.DerivedLaws
public import Std.Tactic.Do.ProofMode
public import Lean.SubExpr
public import Lean.Meta.Basic
public import Lean.Elab.Tactic.Basic

public section

namespace Lean.Elab.Tactic.Do.ProofMode

open Lean Elab Meta
open Std.Do Std.Tactic.Do

@[match_pattern] private def nameAnnotation := `name
@[match_pattern] private def uniqAnnotation := `uniq

structure Hyp where
  name : Name
  uniq : Name -- for display purposes only
  p : Expr

def parseHyp? : Expr → Option Hyp
  | .mdata ⟨[(nameAnnotation, .ofName name), (uniqAnnotation, .ofName uniq)]⟩ p =>
    some ⟨name, uniq, p⟩ -- NB: mdatas are transparent to SubExpr; hence no pos.push
  | _ => none

def Hyp.toExpr (hyp : Hyp) : Expr :=
  .mdata ⟨[(nameAnnotation, .ofName hyp.name), (uniqAnnotation, .ofName hyp.uniq)]⟩ hyp.p

-- set_option pp.all true in
-- #check ⌜True⌝
def emptyHyp (u : Level) (σs : Expr) : Expr := -- ⌜True⌝ standing in for an empty conjunction of hypotheses
  mkApp3 (mkConst ``SVal.curry [u]) (mkApp (mkConst ``ULift [u, 0]) (.sort .zero)) σs <| mkLambda `tuple .default (mkApp (mkConst ``SVal.StateTuple [u]) σs) (mkApp2 (mkConst ``ULift.up [u, 0]) (.sort .zero) (mkConst ``True))
def parseEmptyHyp? : Expr → Option (Level × Expr)
  | mkApp3 (.const ``SVal.curry [u]) (mkApp (.const ``ULift _) (.sort .zero)) σs (.lam _ _ (mkApp2 (.const ``ULift.up _) _ (.const ``True _)) _) => some (u, σs)
  | _ => none

def pushLeftConjunct (pos : SubExpr.Pos) : SubExpr.Pos :=
  pos.pushNaryArg 3 1

def pushRightConjunct (pos : SubExpr.Pos) : SubExpr.Pos :=
  pos.pushNaryArg 3 2

/-- Combine two hypotheses into a conjunction.
Precondition: Neither `lhs` nor `rhs` is empty (`parseEmptyHyp?`). -/
def mkAnd! (u : Level) (σs lhs rhs : Expr) : Expr :=
  mkApp3 (mkConst ``SPred.and [u]) σs lhs rhs

/-- Smart constructor that cancels away empty hypotheses,
along with a proof that `lhs ∧ rhs ⊣⊢ₛ result`. -/
def mkAnd (u : Level) (σs lhs rhs : Expr) : Expr × Expr :=
  if let some _ := parseEmptyHyp? lhs then
    (rhs, mkApp2 (mkConst ``SPred.true_and [u]) σs rhs)
  else if let some _ := parseEmptyHyp? rhs then
    (lhs, mkApp2 (mkConst ``SPred.and_true [u]) σs lhs)
  else
    let result := mkAnd! u σs lhs rhs
    (result, mkApp2 (mkConst ``SPred.bientails.refl [u]) σs result)

def σs.mkType (u : Level) : Expr := mkApp (mkConst ``List [.succ u]) (mkSort (.succ u))
def σs.mkNil (u : Level) : Expr := mkApp (mkConst ``List.nil [.succ u]) (mkSort (.succ u))

def parseAnd? (e : Expr) : Option (Level × Expr × Expr × Expr) :=
      (e.getAppFn.constLevels![0]!, ·) <$> e.app3? ``SPred.and
  <|> (0, σs.mkNil 0, ·) <$> e.app2? ``And

structure MGoal where
  u : Level
  σs : Expr -- Q(List Type)
  hyps : Expr -- A conjunction of hypotheses in `SPred σs`, each carrying a name and uniq as metadata (`parseHyp?`)
  target : Expr -- Q(SPred $σs)
  deriving Inhabited

def parseMGoal? (expr : Expr) : Option MGoal := do
  let some (σs, hyps, target) := expr.consumeMData.app3? ``MGoalEntails | none
  some { u := expr.getAppFn'.constLevels![0]!, σs, hyps, target }

open Tactic in
def ensureMGoal : TacticM (MVarId × MGoal) := do
  let mvar ← getMainGoal
  let goal ← instantiateMVars <| (← mvar.getType)
  if let some goal := parseMGoal? goal then
    return (mvar, goal)
  else
    throwError "Not in proof mode"

def MGoal.strip (goal : MGoal) : Expr := -- omits the .mdata wrapper
  mkApp3 (mkConst ``SPred.entails [goal.u]) goal.σs goal.hyps goal.target

/-- Roundtrips with `parseMGoal?`. -/
def MGoal.toExpr (goal : MGoal) : Expr :=
  mkApp3 (mkConst ``MGoalEntails [goal.u]) goal.σs goal.hyps goal.target

partial def MGoal.findHyp? (goal : MGoal) (name : Name) : Option (SubExpr.Pos × Hyp) := go goal.hyps SubExpr.Pos.root
  where
    go (e : Expr) (p : SubExpr.Pos) : Option (SubExpr.Pos × Hyp) := do
      if let some hyp := parseHyp? e then
        if hyp.name = name then
          return (p, hyp)
        else
          none
      else if let some (_, _, lhs, rhs) := parseAnd? e then
        -- NB: Need to prefer rhs over lhs, like the goal view (Lean.Elab.Tactic.Do.ProofMode.Delab).
        go rhs (pushLeftConjunct p) <|> go lhs (pushRightConjunct p)
      else if let some _ := parseEmptyHyp? e then
        none
      else
        panic! "MGoal.findHyp?: hypothesis without proper metadata: {e}"

def MGoal.checkProof (goal : MGoal) (prf : Expr) (suppressWarning : Bool := false) : MetaM Unit := do
  check prf
  let prf_type ← inferType prf
  unless ← isDefEq goal.toExpr prf_type do
    throwError "MGoal.checkProof: the proof and its supposed type did not match.\ngoal:  {goal.toExpr}\nproof: {prf_type}"
  unless suppressWarning do
    logWarning m!"stray MGoal.checkProof {prf_type} {goal.toExpr}"

def getFreshHypName : TSyntax ``binderIdent → CoreM (Name × Syntax)
  | `(binderIdent| $name:ident) => pure (name.getId, name)
  | stx => return (← mkFreshUserName `h, stx)

partial def betaRevPreservingHypNames (σs' e : Expr) (args : Array Expr) : Expr :=
  if let some (u, _) := parseEmptyHyp? e then
    emptyHyp u σs'
  else if let some hyp := parseHyp? e then
    { hyp with p := hyp.p.betaRev args }.toExpr
  else if let some (u, _σs, lhs, rhs) := parseAnd? e then
    -- _σs = σ :: σs'
    mkAnd! u σs' (betaRevPreservingHypNames σs' lhs args) (betaRevPreservingHypNames σs' rhs args)
  else
    e.betaRev args

def betaPreservingHypNames (σs' e : Expr) (args : Array Expr) : Expr :=
  betaRevPreservingHypNames σs' e args.reverse

def dropStateList (σs : Expr) (n : Nat) : MetaM Expr := do
  let mut σs := σs
  for _ in *...n do
    let some (_type, _σ, σs') := (← whnfR σs).app3? ``List.cons | throwError "Ambient state list not a cons {σs}"
    σs := σs'
  return σs

partial def MGoal.renameInaccessibleHyps (goal : MGoal) (idents : Array (TSyntax ``binderIdent)) : MetaM MGoal := do
  let (hyps, (_, idents)) ← StateT.run (go goal.hyps) ({}, idents) -- NB: idents in reverse order
  unless idents.isEmpty do
    throwError "mrename_i: Could not find inaccessible hypotheses for {idents} in {goal.toExpr}"
  return { goal with hyps := hyps }
  where
    go (H : Expr) : StateT (NameSet × Array (TSyntax ``binderIdent)) MetaM Expr := do
      let mut (shadowed, idents) ← StateT.get
      if idents.isEmpty then
        return H
      if let some _ := parseEmptyHyp? H then
        return H
      if let some hyp := parseHyp? H then
        if hyp.name.hasMacroScopes || shadowed.contains hyp.name then
          if let `(binderIdent| $name:ident) := idents.back! then
            let hyp := { hyp with name := name.getId }
            StateT.set (shadowed, idents.pop)
            return hyp.toExpr
          idents := idents.pop
        StateT.set (shadowed.insert hyp.name, idents)
        return H
      if let some (u, σs, lhs, rhs) := parseAnd? H then
        let rhs ← go rhs -- NB: First go right because those are the "most recent" hypotheses
        let lhs ← go lhs
        return mkAnd! u σs lhs rhs
      return H

def addLocalVarInfo (stx : Syntax) (lctx : LocalContext)
    (expr : Expr) (expectedType? : Option Expr) (isBinder := false) : MetaM Unit := do
  Elab.withInfoContext' (pure ())
    (fun _ =>
      return .inl <| .ofTermInfo
        { elaborator := .anonymous, lctx, expr, stx, expectedType?, isBinder })
    (return .ofPartialTermInfo { elaborator := .anonymous, lctx, stx, expectedType? })

def addHypInfo (stx : Syntax) (σs : Expr) (hyp : Hyp) (isBinder := false) : MetaM Unit := do
  let lctx ← getLCtx
  let ty := mkApp2 (← mkConstWithFreshMVarLevels ``MGoalHypMarker) σs hyp.p
  addLocalVarInfo stx (lctx.mkLocalDecl ⟨hyp.uniq⟩ hyp.name ty) (.fvar ⟨hyp.uniq⟩) ty isBinder
