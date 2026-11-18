/-
Copyright (c) 2026 Lean FRO, LLC. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Elab.Tactic.Grind.Basic
public import Lean.Meta.ExprPattern
import Lean.Elab.Tactic.Grind.SimprocDSL
import Lean.Meta.Sym.Grind
import Lean.Meta.Sym.Simp.Variant
import Lean.Meta.Sym.Simp.Rewrite
import Lean.Meta.Sym.Simp.EvalGround
import Lean.Meta.Sym.Simp.Goal
import Lean.Meta.Sym.Simp.Attr
import Lean.Meta.Sym.Simp.ControlFlow
import Lean.Meta.Sym.Simp.Forall
import Lean.Meta.Tactic.Apply
import Lean.Elab.Tactic.Location
import Lean.Elab.SyntheticMVars
namespace Lean.Elab.Tactic.Grind
open Meta

/--
Low-priority `MonadSym` instance for monads lifting `GrindTacticM` (such as `GrindTacticM` itself),
declared here rather than in `Grind.Basic` to preserve `MonadLiftT MetaM GrindTacticM` resolution
via `TermElabM`.
-/
public instance (priority := low) {m : Type → Type v} [MonadLiftT GrindTacticM m] :
    Meta.MonadSym m where
  liftSym x := liftM (liftSymM x)

/-- Introduces one binder from the main goal, optionally internalizing it into the `grind`
state, and updates the main goal. -/
public def intro1 (internalize : Bool := false) : GrindTacticM (FVarId × Meta.Grind.Goal) := do
  let hygienic := tactic.hygienic.get (← getOptions)
  let goal ← getMainGoal
  match (← liftSymM <| Grind.Goal.introN goal 1 hygienic) with
  | .goal xs goal =>
    let some fvarId := xs[0]? | throwError "`intro1` failed"
    let goal ← if internalize then liftGrindM <| Grind.Goal.internalizeAll goal else pure goal
    replaceMainGoal [goal]
    return (fvarId, goal)
  | .failed => throwError "`intro` failed, no binders to introduce"

def evalIntroCore (internalize : Bool) (ids : TSyntaxArray `Lean.binderIdent) : GrindTacticM Unit := do
  ensureSym
  if ids.isEmpty then
    discard <| intro1 internalize
    return
  let hygienic := tactic.hygienic.get (← getOptions)
  let goal ← getMainGoal
  let names ← ids.mapM fun id => match id with
    | `(binderIdent| $name:ident) => pure name.getId
    | `(binderIdent| $_) => mkFreshBinderNameForTactic `h
  let goal ← match (← liftSymM <| Grind.Goal.intros goal names hygienic) with
    | .goal _ goal => pure goal
    | .failed => throwError "`intro` failed"
  let goal ← if internalize then liftGrindM <| Grind.Goal.internalizeAll goal else pure goal
  replaceMainGoal [goal]

@[builtin_grind_tactic Parser.Tactic.Grind.symIntro] def evalSymIntro : GrindTactic := fun stx => do
  -- syntax: "intro" ("(" &"internalize" " := " (&"true" <|> &"false") ")")? binderIdent*
  match stx with
  | `(grind| intro $ids:binderIdent*) => evalIntroCore true ids
  | `(grind| intro (internalize := false) $ids:binderIdent*) => evalIntroCore false ids
  | `(grind| intro (internalize := true) $ids:binderIdent*) => evalIntroCore true ids
  | _ => throwUnsupportedSyntax

def evalIntrosCore (internalize : Bool) : GrindTacticM Unit := do
  ensureSym
  let hygienic := tactic.hygienic.get (← getOptions)
  let goal ← getMainGoal
  match (← liftSymM <| Grind.Goal.intros goal #[] hygienic) with
  | .goal _ goal =>
    let goal ← if internalize then liftGrindM <| Grind.Goal.internalizeAll goal else pure goal
    replaceMainGoal [goal]
  | .failed => throwError "`intros` failed"

@[builtin_grind_tactic Parser.Tactic.Grind.symIntros] def evalSymIntros : GrindTactic := fun stx => do
  match stx with
  | `(grind| intros) => evalIntrosCore true
  | `(grind| intros (internalize := false)) => evalIntrosCore false
  | `(grind| intros (internalize := true)) => evalIntrosCore true
  | _ => throwUnsupportedSyntax

/-- Returns the instantiated target type of the main goal. -/
public def getMainTarget : GrindTacticM Expr := do
  instantiateMVars (← (← getMainGoal).mvarId.getType)

/-- Head-beta-reduces the target of the main goal if it is a head-beta redex, preserving
maximally shared representation via `Sym.share`. -/
public def headBetaMainGoal : GrindTacticM Unit := do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.mvarId.getType)
  if ty.isHeadBetaTarget then
    let mvarId ← goal.mvarId.replaceTargetDefEq (← liftSymM (Sym.share ty.headBeta))
    replaceMainGoal [{ goal with mvarId }]

/-- Get or create a `BackwardRule` for a declaration, using the name cache. -/
public def getOrCreateBackwardRule (declName : Name) : GrindTacticM Sym.BackwardRule := do
  if let some rule := (← get).cache.backwardRuleName.find? declName then
    return rule
  let rule ← Sym.mkBackwardRuleFromDecl declName
  modify fun s => { s with cache.backwardRuleName := s.cache.backwardRuleName.insert declName rule }
  return rule

/--
Get or create a `BackwardRule` for a term. An identifier that is not shadowed by a local
declaration of the main goal and resolves to a global constant uses the name cache
(`getOrCreateBackwardRule`); any other term is elaborated in the main goal's context and cached by
syntax position.
-/
public def getOrCreateBackwardRuleFromTerm (term : Syntax) : GrindTacticM Sym.BackwardRule :=
  withMainContext do
  if let `($id:ident) := term then
    if ((← getLCtx).findFromUserName? id.getId).isNone then
      if let some declName ← observing? (realizeGlobalConstNoOverloadWithInfo id) then
        return ← getOrCreateBackwardRule declName
  let startPos := term.getPos?.map (·.byteIdx) |>.getD 0
  let endPos := term.getTailPos?.map (·.byteIdx) |>.getD 0
  let pos := (startPos, endPos)
  if let some rule := (← get).cache.backwardRuleSyntax.find? pos then
    return rule
  let e ← Term.elabTerm term none
  Term.synthesizeSyntheticMVars (postpone := .no)
  let rule ← Sym.mkBackwardRuleFromExpr (← instantiateMVars e)
  modify fun s => { s with cache.backwardRuleSyntax := s.cache.backwardRuleSyntax.insert pos rule }
  return rule

/-- Applies a `Sym.BackwardRule` to the main goal, replacing it with the resulting subgoals. -/
public def applyBackwardRule (rule : Sym.BackwardRule) : GrindTacticM Unit := do
  let goal ← getMainGoal
  match (← liftSymM <| Grind.Goal.apply goal rule) with
  | .goals subgoals => replaceMainGoal subgoals
  | .failed => throwError "`apply` failed, rule is not applicable"

/-- Applies a cached `Sym.BackwardRule` built from declaration `declName` to the main goal. -/
public def applyDecl (declName : Name) : GrindTacticM Unit := do
  applyBackwardRule (← getOrCreateBackwardRule declName)

/-- Attempts to close the main goal by reflexivity (`Eq.refl`). Returns `true` on success. -/
public def refl? : GrindTacticM Bool := do
  let goal ← getMainGoal
  let rule ← getOrCreateBackwardRule ``Eq.refl
  let res ← observing? do
    match (← liftSymM <| Grind.Goal.apply goal rule) with
    | .goals [] => replaceMainGoal []
    | _ => failure
  return res.isSome

/-- Attempts to close the main goal using a matching hypothesis in the local context.
Returns `true` on success. -/
public def assumption? : GrindTacticM Bool := do
  let goal ← getMainGoal
  if ← goal.assumption then
    replaceMainGoal []
    return true
  return false

/--
Runs `step` repeatedly until no unsolved goals remain. If `headBeta` is `true`, the main goal's
target is head-beta-reduced (see `headBetaMainGoal`) before each `step`.
-/
public def whileGoals (step : GrindTacticM Unit) (headBeta : Bool := false) :
    GrindTacticM Unit := do
  while !(← getUnsolvedGoals).isEmpty do
    if headBeta then headBetaMainGoal
    step

/--
Runs `tac` on the main goal, then runs `first` focused on the first resulting subgoal and `rest`
focused on each remaining one (skipping subgoals that `first` already solved). The resulting
unsolved goals replace the main goal, in order.
-/
public def andThenSubgoals (tac : GrindTacticM Unit) (first : GrindTacticM Unit)
    (rest : GrindTacticM Unit := pure ()) : GrindTacticM Unit := focus do
  tac
  let g :: gs ← getUnsolvedGoals | return
  setGoals [g]
  first
  let mut acc := (← getUnsolvedGoals).toArray
  for g in gs do
    setGoals [g]
    if (← getUnsolvedGoals).isEmpty then continue
    rest
    acc := acc ++ (← getUnsolvedGoals)
  setGoals acc.toList

/--
Try `f h ty` on each non-implementation-detail hypothesis `(h, ty)` of the main goal and return
the first succeeding result `some r`.

Hypotheses are tried newest first by default (`reverse := true`); pass `reverse := false` for
oldest first. Free variables listed in `except` are skipped, and assigned metavariables in `ty`
are instantiated before `f` is invoked inside the main goal's local context.

Execution runs inside `Term.withoutTacticIncrementality true`, `Term.withoutErrToSorry`, and
`withoutRecover`. If an arm fails, `Grind.SavedState` is atomically rolled back with
`restoreInfo := true` before trying the next hypothesis. Returns `none` if no hypothesis succeeds.
-/
public def firstHyp? (f : Expr → Expr → GrindTacticM α)
    (reverse : Bool := true) (except : List Expr := []) : GrindTacticM (Option α) :=
  Term.withoutTacticIncrementality true <| Term.withoutErrToSorry <| withoutRecover do
    (← getMainGoal).mvarId.withContext do
      let hyps ← (Meta.localHypTypes (reverse := reverse) (except := except) :
        MetaM (Array (Expr × Expr)))
      let s ← Grind.saveState
      for (h, ty) in hyps do
        if let some r ← Grind.tryCatch (some <$> f h ty) fun _ => do
            s.restore (restoreInfo := true)
            return none then
          return some r
      return none

/--
Like `Lean.Elab.Tactic.Grind.firstHyp?`, but throws `"firstHyp: no hypothesis matched"` if no
hypothesis succeeds.
-/
public def firstHyp (f : Expr → Expr → GrindTacticM α)
    (reverse : Bool := true) (except : List Expr := []) : GrindTacticM α := do
  match ← firstHyp? f (reverse := reverse) (except := except) with
  | some a => return a
  | none   => throwError "firstHyp: no hypothesis matched"

@[builtin_grind_tactic Parser.Tactic.Grind.symApply] def evalSymApply : GrindTactic := fun stx => do
  ensureSym
  let `(grind| apply $term:term) := stx | throwUnsupportedSyntax
  applyBackwardRule (← getOrCreateBackwardRuleFromTerm term)

@[builtin_grind_tactic Parser.Tactic.Grind.symInternalize] def evalSymInternalize : GrindTactic := fun stx => do
  ensureSym
  let goal ← getMainGoal
  let num := if stx[1].isNone then 1 else stx[1][0].toNat
  let goal ← liftGrindM <| Grind.Goal.internalize goal num
  replaceMainGoal [goal]

@[builtin_grind_tactic Parser.Tactic.Grind.symInternalizeAll] def evalSymInternalizeAll : GrindTactic := fun _ => do
  ensureSym
  let goal ← getMainGoal
  let goal ← liftGrindM <| Grind.Goal.internalizeAll goal
  replaceMainGoal [goal]

@[builtin_grind_tactic Parser.Tactic.Grind.symByContra] def evalSymByContra : GrindTactic := fun _ => do
  ensureSym
  let goal ← getMainGoal
  let target ← goal.mvarId.getType
  if target.isFalse then
    throwError "`by_contra` failed, target is already `False`"
  -- If target is not a proposition, apply exfalso first
  let mvarId ← if (← isProp target) then pure goal.mvarId else goal.mvarId.exfalso
  let some mvarId ← mvarId.byContra?
    | throwError "`by_contra` failed"
  -- byContra? produces `⊢ ¬target → False`, introduce the negated hypothesis
  let (_, mvarId) ← mvarId.intro1
  let goal := { goal with mvarId }
  -- Internalize the negated hypothesis so the E-graph can detect contradictions
  let goal ← liftGrindM <| Grind.Goal.internalizeAll goal
  replaceMainGoal [goal]

section
open Sym.Simp

def trivialSimproc : Simproc := fun _ =>
  return .rfl

def elabOptSimproc (stx? : Option Syntax) : GrindTacticM Simproc := do
  let some stx := stx? | return trivialSimproc
  elabSymSimproc stx

def elabOptDischarger (stx? : Option Syntax) : GrindTacticM Discharger := do
  let some stx := stx? | return dischargeNone
  elabSymDischarger stx

def resolveExtraTheorems (ids? :  Option (Array (TSyntax `ident))) : GrindTacticM (Array ExtraTheorem × Array Theorem) := do
  let some ids := ids? | return (#[], #[])
  let mut extras := #[]
  let mut thms := #[]
  let lctx ← getLCtx
  for id in ids do
    if let some decl := lctx.findFromUserName? id.getId then
      extras := extras.push <| .fvar decl.fvarId
      thms := thms.push (← mkTheoremFromExpr decl.toExpr)
    else
      let declName ← realizeGlobalConstNoOverload id
      extras := extras.push <| .const declName
      thms := thms ++ (← mkTheoremsFromDecl declName)
  return (extras, thms)

/-- Appends the extra theorems `extraThms` to `post`, discharging their side conditions with `d`. -/
def addExtraTheorems (post : Simproc) (extraThms : Array Theorem) (d : Discharger := dischargeNone) : GrindTacticM Simproc := do
  if extraThms.isEmpty then return post
  let mut thms : Theorems := {}
  for thm in extraThms do
    thms := thms.insert thm
  return post >> thms.rewrite d

/--
Methods of the default `Sym.simp` variant. The discharger `d` is used for the side conditions
of the `sym_simp` theorems and of the extra theorems `extraThms`.
-/
def mkSimpDefaultMethods (extraThms : Array Theorem) (d : Discharger) : GrindTacticM Sym.Simp.Methods := do
  let thms ← getSymSimpTheorems
  let pre := simpControl >> simpArrowTelescope
  let post ← addExtraTheorems (evalGround >> thms.rewrite d) extraThms d
  return { pre, post }

/--
`grind` configuration of the default `Sym.simp` discharger. Side conditions are proved from the
internalized context and a single round of E-matching with few instances. A failing attempt
redoes the whole search, since the `grind` state is discarded after each attempt, so the search
is kept small.
-/
def defaultDischargerConfig (cfg : Lean.Grind.Config) : Lean.Grind.Config :=
  { cfg with ematch := 1, gen := 1, genLocal := 1, instances := 20 }

/--
Creates the discharger of the default `Sym.simp` variant: `grind` on `goal` with
`defaultDischargerConfig`. See `Grind.Goal.mkSymSimpDischarger`.
-/
def mkDefaultDischarger (goal : Meta.Grind.Goal) : Meta.Grind.GrindM Discharger :=
  withTheReader Meta.Grind.Context (fun ctx => { ctx with config := defaultDischargerConfig ctx.config })
    goal.mkSymSimpDischarger

def elabSimpVariant (variantName : Name) (extraThms : Array Theorem) : GrindTacticM (Sym.Simp.Methods × Sym.Simp.Config) := do
  if variantName.isAnonymous then
    let d ← liftGrindM <| mkDefaultDischarger (← getMainGoal)
    return (← mkSimpDefaultMethods extraThms d, {})
  let some v := getSymSimpVariant? (← getEnv) variantName
    | throwError "unknown Sym.simp variant `{variantName}`"
  let pre ← elabOptSimproc v.pre?
  let post ← addExtraTheorems (← elabOptSimproc v.post?) extraThms (← elabOptDischarger v.discharger?)
  return ({ pre, post}, v.config)

/--
Simplifies `goal`'s target with `methods` and `config`. Returns `none` if `goal` was closed, or
`some goal'` (equal to `goal` if no progress was made).

When `cacheKey?` is `some k`, the `Sym.Simp.State` stored in `State.cache.simpState` under the key
`{ variant := k, extras := #[] }` is reused and the updated state is stored back. This key space is
shared with `sym => simp`, which uses the variant name (or `.anonymous` for the default variant) as
`variant`, so `k` must not be `.anonymous` or the name of a `Sym.simp` variant, and must uniquely
identify the pair `(methods, config)`: reusing `k` with different methods or configuration would
reuse cache entries computed by a different simplifier.
-/
public def simpGoal (goal : Meta.Grind.Goal) (methods : Sym.Simp.Methods)
    (config : Sym.Simp.Config := {}) (cacheKey? : Option Name := none) :
    GrindTacticM (Option Meta.Grind.Goal) := do
  let simpState : Sym.Simp.State ← match cacheKey? with
    | some k =>
      let key : SimpCacheKey := { variant := k, extras := #[] }
      pure <| (← get).cache.simpState[key]?.getD {}
    | none => pure {}
  let (r, simpState) ← liftSymM <| goal.withContext do
    Sym.Simp.SimpM.run (methods := methods) (config := config) (s := simpState) do
      (← Sym.Simp.simp (← goal.mvarId.getType)).toSimpGoalResult goal.mvarId
  if let some k := cacheKey? then
    let key : SimpCacheKey := { variant := k, extras := #[] }
    modify fun s => { s with cache.simpState := s.cache.simpState.insert key simpState }
  match r with
  | .closed => return none
  | .noProgress => return some goal
  | .goal mvarId => return some { goal with mvarId }

/--
Simplifies the main goal's target with `methods` and `config` (optionally threading a persistent
cache under `cacheKey?`), updating the main goal. Returns `true` if the main goal was closed.
-/
public def simpMainGoal (methods : Sym.Simp.Methods) (config : Sym.Simp.Config := {})
    (cacheKey? : Option Name := none) : GrindTacticM Bool := do
  let goal ← getMainGoal
  match ← simpGoal goal methods config cacheKey? with
  | none => replaceMainGoal []; return true
  | some goal' =>
    if goal'.mvarId != goal.mvarId then
      replaceMainGoal [goal']
    return false

@[builtin_grind_tactic Parser.Tactic.Grind.symSimp] def evalSymSimp : GrindTactic := fun stx => withMainContext do
  ensureSym
  let `(grind| simp $[$variantId?]? $[[ $[$extraIds],* ]]?) := stx | throwUnsupportedSyntax
  -- Resolve variant
  let variantName := variantId?.map (·.getId) |>.getD .anonymous
  -- Resolve extra theorems (local hypotheses first, then global constants)
  let (extras, thms) ← resolveExtraTheorems extraIds
  -- Cache lookup/creation
  let cacheKey : SimpCacheKey := { variant := variantName, extras }
  let simpState := (← get).cache.simpState[cacheKey]?.getD {}
  let (methods, config) ← elabSimpVariant variantName thms
  let goal ← getMainGoal
  let (simpResult, simpState) ← liftGrindM <| goal.withContext do
    Sym.Simp.SimpM.run (Sym.Simp.simp (← goal.mvarId.getType)) methods config simpState
  -- Save updated cache
  modify fun s => { s with cache.simpState := s.cache.simpState.insert cacheKey simpState }
  -- Apply result to goal
  match (← liftGrindM <| Sym.Simp.Result.toSimpGoalResult simpResult goal.mvarId) with
  | .closed => replaceMainGoal []
  | .goal mvarId => replaceMainGoal [{ goal with mvarId }]
  | .noProgress => throwError "`Sym.simp` made no progress"

end

end Lean.Elab.Tactic.Grind
