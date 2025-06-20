/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Sebastian Graf
-/
prelude
import Std.Do.SPred.DerivedLaws

import Lean.Meta
open Lean Elab Meta

namespace Std.Do

/-- Tautology in `SPred` as a definition. -/
abbrev SPred.tautological {σs : List Type} (Q : SPred σs) : Prop := ⊢ₛ Q

class PropAsSPredTautology (φ : Prop) {σs : outParam (List Type)} (P : outParam (SPred σs)) : Prop where
  iff : φ ↔ ⊢ₛ P

instance : PropAsSPredTautology (σs := []) φ φ where
  iff := true_imp_iff.symm

instance : PropAsSPredTautology (P ⊢ₛ Q) spred(P → Q) where
  iff := (SPred.entails_true_intro P Q).symm

instance : PropAsSPredTautology (⊢ₛ P) P where
  iff := Iff.rfl

end Std.Do

namespace Lean.Elab.Tactic.Do.ProofMode
open Std.Do

theorem start_entails {φ : Prop} [PropAsSPredTautology φ P] : (⊢ₛ P) → φ :=
  PropAsSPredTautology.iff.mpr

theorem elim_entails {φ : Prop} [PropAsSPredTautology φ P] : φ → (⊢ₛ P) :=
  PropAsSPredTautology.iff.mp

@[match_pattern] def nameAnnotation := `name
@[match_pattern] def uniqAnnotation := `uniq

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

/-- An elaborator to create a new named hypothesis for an `MGoal` context. -/
elab "mk_hyp " name:ident " := " e:term : term <= ty? => do
  let e ← Lean.Elab.Term.elabTerm e ty?
  let uniq ← mkFreshId
  return (Hyp.mk name.getId uniq e).toExpr

-- set_option pp.all true in
-- #check ⌜True⌝
def emptyHyp (σs : Expr) : Expr := -- ⌜True⌝ standing in for an empty conjunction of hypotheses
  mkApp3 (mkConst ``SVal.curry) (.sort .zero) σs <| mkLambda `escape .default (mkApp (mkConst ``SVal.StateTuple) σs) (mkConst ``True)
def parseEmptyHyp? : Expr → Option Expr
  | mkApp3 (.const ``SVal.curry _) (.sort .zero) σs (.lam _ _ (.const ``True _) _) => some σs
  | _ => none

def pushLeftConjunct (pos : SubExpr.Pos) : SubExpr.Pos :=
  pos.pushNaryArg 3 1

def pushRightConjunct (pos : SubExpr.Pos) : SubExpr.Pos :=
  pos.pushNaryArg 3 2

/-- Combine two hypotheses into a conjunction.
Precondition: Neither `lhs` nor `rhs` is empty (`parseEmptyHyp?`). -/
def mkAnd! (σs lhs rhs : Expr) : Expr :=
  mkApp3 (mkConst ``SPred.and) σs lhs rhs

/-- Smart constructor that cancels away empty hypotheses,
along with a proof that `lhs ∧ rhs ⊣⊢ₛ result`. -/
def mkAnd (σs lhs rhs : Expr) : Expr × Expr :=
  if let some _ := parseEmptyHyp? lhs then
    (rhs, mkApp2 (mkConst ``SPred.true_and) σs rhs)
  else if let some _ := parseEmptyHyp? rhs then
    (lhs, mkApp2 (mkConst ``SPred.and_true) σs lhs)
  else
    let result := mkAnd! σs lhs rhs
    (result, mkApp2 (mkConst ``SPred.bientails.refl) σs result)

def σs.mkType : Expr := mkApp (mkConst ``List [.succ .zero]) (mkSort (.succ .zero))
def σs.mkNil : Expr := mkApp (mkConst ``List.nil [.succ .zero]) (mkSort (.succ .zero))

def parseAnd? (e : Expr) : Option (Expr × Expr × Expr) :=
  e.app3? ``SPred.and <|> (σs.mkNil, ·) <$> e.app2? ``And

structure MGoal where
  σs : Expr -- Q(List Type)
  hyps : Expr -- A conjunction of hypotheses in `SPred σs`, each carrying a name and uniq as metadata (`parseHyp?`)
  target : Expr -- Q(SPred $σs)
  deriving Inhabited

/-- This is the same as `SPred.entails`.
This constant is used to detect `SPred` proof mode goals. -/
abbrev MGoalEntails := @SPred.entails

def parseMGoal? (expr : Expr) : Option MGoal := do
  let some (σs, hyps, target) := expr.consumeMData.app3? ``MGoalEntails | none
  some { σs, hyps, target }

open Tactic in
def ensureMGoal : TacticM (MVarId × MGoal) := do
  let mvar ← getMainGoal
  let goal ← instantiateMVars <| (← mvar.getType)
  if let some goal := parseMGoal? goal then
    return (mvar, goal)
  else
    throwError "Not in proof mode"

def MGoal.strip (goal : MGoal) : Expr := -- omits the .mdata wrapper
  mkApp3 (mkConst ``SPred.entails) goal.σs goal.hyps goal.target

/-- Roundtrips with `parseMGoal?`. -/
def MGoal.toExpr (goal : MGoal) : Expr :=
  mkApp3 (mkConst ``MGoalEntails) goal.σs goal.hyps goal.target

partial def MGoal.findHyp? (goal : MGoal) (name : Name) : Option (SubExpr.Pos × Hyp) := go goal.hyps SubExpr.Pos.root
  where
    go (e : Expr) (p : SubExpr.Pos) : Option (SubExpr.Pos × Hyp) := do
      if let some hyp := parseHyp? e then
        if hyp.name = name then
          return (p, hyp)
        else
          none
      else if let some (_, lhs, rhs) := parseAnd? e then
        -- NB: Need to prefer rhs over lhs, like the goal view (Lean.Elab.Tactic.Do.ProofMode.Display).
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
  if let some _σs := parseEmptyHyp? e then
    emptyHyp σs'
  else if let some hyp := parseHyp? e then
    { hyp with p := hyp.p.betaRev args }.toExpr
  else if let some (_σs, lhs, rhs) := parseAnd? e then
    -- _σs = σ :: σs'
    mkAnd! σs' (betaRevPreservingHypNames σs' lhs args) (betaRevPreservingHypNames σs' rhs args)
  else
    e.betaRev args

def betaPreservingHypNames (σs' e : Expr) (args : Array Expr) : Expr :=
  betaRevPreservingHypNames σs' e args.reverse

def dropStateList (σs : Expr) (n : Nat) : MetaM Expr := do
  let mut σs := σs
  for _ in [:n] do
    let some (_type, _σ, σs') := (← whnfR σs).app3? ``List.cons | throwError "Ambient state list not a cons {σs}"
    σs := σs'
  return σs

/-- This is only used for display purposes, so that we can render context variables that appear
to have type `A : PROP` even though `PROP` is not a type. -/
def HypMarker {σs : List Type} (_A : SPred σs) : Prop := True

def addLocalVarInfo (stx : Syntax) (lctx : LocalContext)
    (expr : Expr) (expectedType? : Option Expr) (isBinder := false) : MetaM Unit := do
  Elab.withInfoContext' (pure ())
    (fun _ =>
      return .inl <| .ofTermInfo
        { elaborator := .anonymous, lctx, expr, stx, expectedType?, isBinder })
    (return .ofPartialTermInfo { elaborator := .anonymous, lctx, stx, expectedType? })

def addHypInfo (stx : Syntax) (σs : Expr) (hyp : Hyp) (isBinder := false) : MetaM Unit := do
  let lctx ← getLCtx
  let ty := mkApp2 (mkConst ``HypMarker) σs hyp.p
  addLocalVarInfo stx (lctx.mkLocalDecl ⟨hyp.uniq⟩ hyp.name ty) (.fvar ⟨hyp.uniq⟩) ty isBinder
