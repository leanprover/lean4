/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Cases
public import Lean.Meta.Tactic.Simp.Rewrite
import Lean.Meta.Tactic.Simp.Main
import Lean.Meta.FunInfo
public section
namespace Lean.Meta

inductive SplitKind where
  | ite | match | both

def SplitKind.considerIte : SplitKind → Bool
  | .ite | .both => true
  | _ => false

def SplitKind.considerMatch : SplitKind → Bool
  | .match | .both => true
  | _ => false

namespace FindSplitImpl

structure Context where
  exceptionSet : ExprSet := {}
  kind : SplitKind := .both

unsafe abbrev FindM := ReaderT Context $ StateT (PtrSet Expr) MetaM

/--
Checks whether `e` is a candidate for `split`.
Returns `some e'` if a prefix is a candidate.
Example: suppose `e` is `(if b then f else g) x`, then
the result is `some e'` where `e'` is the subterm `(if b then f else g)`
-/
private def isCandidate? (env : Environment) (ctx : Context) (e : Expr) : Option Expr := Id.run do
  let ret (e : Expr) : Option Expr :=
    if ctx.exceptionSet.contains e then none else some e
  if ctx.kind.considerIte then
    if e.isAppOf ``ite || e.isAppOf ``dite then
      let numArgs := e.getAppNumArgs
      if numArgs >= 5 && !(e.getArg! 1 5).hasLooseBVars then
        return ret (e.getBoundedAppFn (numArgs - 5))
  if ctx.kind.considerMatch then
    if let some info := isMatcherAppCore? env e then
      let args := e.getAppArgs
      for i in info.getFirstDiscrPos...(info.getFirstDiscrPos + info.numDiscrs) do
        if args[i]!.hasLooseBVars then
          return none
      return ret (e.getBoundedAppFn (args.size - info.arity))
  return none

@[inline] unsafe def checkVisited (e : Expr) : OptionT FindM Unit := do
  if (← get).contains e then
    failure
  modify fun s => s.insert e

unsafe def visit (e : Expr) : OptionT FindM Expr := do
  checkVisited e
  if let some e := isCandidate? (← getEnv) (← read) e then
    return e
  else
    -- We do not look for split candidates in proofs.
    unless e.hasLooseBVars do
      if (← isProof e) then
        failure
    match e with
    | .lam _ _ b _ | .proj _ _ b -- We do not look for split candidates in the binder of lambdas.
    | .mdata _ b       => visit b
    | .forallE _ d b _ => visit d <|> visit b -- We want to look for candidates at `A → B`
    | .letE _ _ v b _  => visit v <|> visit b
    | .app ..          => visitApp? e
    | _                => failure
where
  visitApp? (e : Expr) : FindM (Option Expr) :=
    e.withApp fun f args => do
    -- See comment at `Canonicalizer.lean` regarding the case where
    -- `f` has loose bound variables.
    let info ← if f.hasLooseBVars then
      pure {}
    else
      getFunInfo f
    for u : i in *...args.size do
      let arg := args[i]
      if h : i < info.paramInfo.size then
        let info := info.paramInfo[i]
        unless info.isProp do
          if info.isExplicit then
            let some found ← visit arg | pure ()
            return found
      else
        let some found ← visit arg | pure ()
        return found
    visit f

end FindSplitImpl

/-- Return an `if-then-else` or `match-expr` to split. -/
partial def findSplit? (e : Expr) (kind : SplitKind := .both) (exceptionSet : ExprSet := {}) : MetaM (Option Expr) := do
  go (← instantiateMVars e)
where
  go (e : Expr) : MetaM (Option Expr) := do
    if let some target ← find? e then
      if target.isIte || target.isDIte then
        let cond := target.getArg! 1 5
        -- Try to find a nested `if` in `cond`
        return (← go cond).getD target
      else
        return some target
    else
      return none

  find? (e : Expr) : MetaM (Option Expr) := do
    let some candidate ← unsafe FindSplitImpl.visit e { kind, exceptionSet } |>.run' mkPtrSet
      | return none
    trace[split.debug] "candidate:{indentExpr candidate}"
    return some candidate

/-- Return the condition and decidable instance of an `if` expression to case split. -/
private partial def findIfToSplit? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  if let some iteApp ← findSplit? e .ite then
    let cond := iteApp.getArg! 1 5
    let dec := iteApp.getArg! 2 5
    return (cond, dec)
  else
    return none

register_builtin_option backward.split : Bool := {
  defValue := true
  descr    := "use the old semantics for the `split` tactic where nested `if-then-else` terms could be simplified too"
}

namespace SplitIf
/--
The `Simp.Context` that used to be used with `simpIf` methods. It contains all congruence theorems, but
just the rewriting rules for reducing `if` expressions.
This function is only used when the old `split` tactic behavior is enabled.
-/
def getSimpContext : MetaM Simp.Context := do
  let mut s : SimpTheorems := {}
  s ← s.addConst ``if_pos
  s ← s.addConst ``if_neg
  s ← s.addConst ``dif_pos
  s ← s.addConst ``dif_neg
  Simp.mkContext
   (simpTheorems  := #[s])
    (congrTheorems := (← getSimpCongrTheorems))
    (config        := { Simp.neutralConfig with dsimp := false, letToHave := true })

/--
Default `Simp.Context` for `simpIf` methods. It contains all congruence theorems, but
without rewriting rules. We use simprocs to reduce the if-then-else terms -/
private def getSimpContext' : MetaM Simp.Context := do
  Simp.mkContext
    (simpTheorems  := {})
    (congrTheorems := (← getSimpCongrTheorems))
    (config        := { Simp.neutralConfig with dsimp := false, letToHave := true })

/--
  Default `discharge?` function for `simpIf` methods.
  It only uses hypotheses from the local context that have `index < numIndices`.
  It is effective after a case-split.

  Remark: when `simp` goes inside binders it adds new local declarations to the
  local context. We don't want to use these local declarations since the cached result
  would depend on them (see issue #3229). `numIndices` is the size of the local
  context `decls` field before we start the simplifying the expression.

  Remark: this function is now private, and we should use `mkDischarge?`.
-/
private def discharge? (numIndices : Nat) (useDecide : Bool) : Simp.Discharge := fun prop => do
  let prop ← instantiateMVars prop
  trace[Meta.Tactic.splitIf] "discharge? {prop}, {prop.notNot?}"
  if useDecide then
    let prop ← instantiateMVars prop
    if !prop.hasFVar && !prop.hasMVar then
      let d ← mkDecide prop
      let r ← withDefault <| whnf d
      if r.isConstOf ``true then
        return some <| mkApp3 (mkConst ``of_decide_eq_true) prop d.appArg! (← mkEqRefl (mkConst ``true))
  (← getLCtx).findDeclRevM? fun localDecl => do
     if localDecl.index ≥ numIndices || localDecl.isAuxDecl then
       return none
     else if (← isDefEq prop localDecl.type) then
       return some localDecl.toExpr
     else match prop.notNot? with
       | none => return none
       | some arg =>
         if (← isDefEq arg localDecl.type) then
           return some (mkApp2 (mkConst ``not_not_intro) arg localDecl.toExpr)
         else
           return none

private def reduceIte' (numIndices : Nat) (useDecideBool : Bool) : Simp.Simproc := fun e => do
  let_expr f@ite α c i tb eb ← e | return .continue
  let us := f.constLevels!
  if let some h ← discharge? numIndices useDecideBool c then
    let h := mkApp6 (mkConst ``if_pos us) c i h α tb eb
    return .done { expr := tb, proof? := some h }
  else if let some h ← discharge? numIndices useDecideBool (mkNot c) then
    let h := mkApp6 (mkConst ``if_neg us) c i h α tb eb
    return .done { expr := eb, proof? := some h }
  else
    -- `split` may have selected an `if-then-else` nested in `c`.
    let r ← Simp.simp c
    if r.expr == c then
      return .done { expr := e }
    else
      let c' := r.expr
      let dec := mkApp (mkConst ``Decidable) c'
      let .some i' ← trySynthInstance dec | return .done { expr := e }
      let h := mkApp8 (mkConst ``ite_cond_congr us) α c c' i i' tb eb (← r.getProof)
      let e' := mkApp5 f α c' i' tb eb
      return .done { expr := e', proof? := some h }

private def getBinderName (e : Expr) : MetaM Name := do
  let .lam n _ _ _ := e | mkFreshUserName `h
  return n

private def reduceDIte' (numIndices : Nat) (useDecideBool : Bool) : Simp.Simproc := fun e => do
  let_expr f@dite α c i tb eb ← e | return .continue
  let us := f.constLevels!
  if let some h ← discharge? numIndices useDecideBool c then
    let e' := mkApp tb h |>.headBeta
    let h := mkApp6 (mkConst ``dif_pos us) c i h α tb eb
    return .done { expr := e', proof? := some h }
  else if let some h ← discharge? numIndices useDecideBool (mkNot c) then
    let e' := mkApp eb h |>.headBeta
    let h := mkApp6 (mkConst ``dif_neg us) c i h α tb eb
    return .done { expr := e', proof? := some h }
  else
    -- `split` may have selected an `if-then-else` nested in `c`.
    let r ← Simp.simp c
    if r.expr == c then
      return .done { expr := e }
    else
      let c' := r.expr
      let h ← r.getProof
      let dec := mkApp (mkConst ``Decidable) c'
      let .some i' ← trySynthInstance dec | return .done { expr := e }
      let tb' := mkApp tb (mkApp4 (mkConst ``Eq.mpr_prop) c c' h (mkBVar 0)) |>.headBeta
      let tb' := mkLambda (← getBinderName tb) .default c' tb'
      let eb' := mkApp eb (mkApp4 (mkConst ``Eq.mpr_not) c c' h (mkBVar 0)) |>.headBeta
      let eb' := mkLambda (← getBinderName eb) .default (mkNot c') eb'
      let e' := mkApp5 f α c' i' tb' eb'
      let h := mkApp8 (mkConst ``dite_cond_congr us) α c c' i i' tb eb h
      return .done { expr := e', proof? := some h }

private def getSimprocs (numIndices : Nat) (useDecide : Bool) : MetaM (Array Simprocs) := do
  let s : Simprocs := {}
  let s := s.addCore #[.const ``ite 5, .star, .star, .star, .star, .star] ``reduceIte' (post := false) (.inl <| reduceIte' numIndices useDecide)
  let s := s.addCore #[.const ``dite 5, .star, .star, .star, .star, .star] ``reduceDIte' (post := false) (.inl <| reduceDIte' numIndices useDecide)
  return #[s]

def mkDischarge? (useDecide := false) : MetaM Simp.Discharge :=
  return discharge? (← getLCtx).numIndices useDecide

def splitIfAt? (mvarId : MVarId) (e : Expr) (hName? : Option Name) : MetaM (Option (ByCasesSubgoal × ByCasesSubgoal)) := mvarId.withContext do
  let e ← instantiateMVars e
  if let some (cond, decInst) ← findIfToSplit? e then
    let hName ← match hName? with
      | none       => mkFreshUserName `h
      | some hName => pure hName
    trace[Meta.Tactic.splitIf] "splitting on {decInst}"
    return some (← mvarId.byCasesDec cond decInst hName)
  else
    trace[Meta.Tactic.splitIf] "could not find if to split:{indentExpr e}"
    return none

end SplitIf

open SplitIf

private def getNumIndices (mvarId : MVarId) : MetaM Nat :=
  mvarId.withContext do return (← getLCtx).numIndices

/--
Simplify the `if-then-else` targeted by the `split` tactic. If `useNewSemantics` is `true`, the flag
`backward.split` is ignored.
-/
def simpIfTarget (mvarId : MVarId) (useDecide := false) (useNewSemantics := false) : MetaM MVarId := do
  if useNewSemantics || !backward.split.get (← getOptions) then
    let ctx ← getSimpContext'
    let numIndices ← getNumIndices mvarId
    let s ← getSimprocs numIndices useDecide
    let (some mvarId', _) ← simpTarget mvarId ctx s (mayCloseGoal := false) | unreachable!
    return mvarId'
  else
    let mut ctx ← getSimpContext
    let (some mvarId', _) ← simpTarget mvarId ctx {} (← mvarId.withContext <| mkDischarge? useDecide) (mayCloseGoal := false) | unreachable!
    return mvarId'

/--
Simplify the `if-then-else` targeted by the `split` tactic. If `useNewSemantics` is `true`, the flag
`backward.split` is ignored.
-/
def simpIfLocalDecl (mvarId : MVarId) (fvarId : FVarId) (useNewSemantics := false) : MetaM MVarId := do
  if useNewSemantics || !backward.split.get (← getOptions) then
    let ctx ← getSimpContext'
    let numIndices ← getNumIndices mvarId
    let s ← getSimprocs numIndices (useDecide := false)
    let (some (_, mvarId'), _) ← simpLocalDecl mvarId fvarId ctx s (mayCloseGoal := false) | unreachable!
    return mvarId'
  else
    let mut ctx ← getSimpContext
    let (some (_, mvarId'), _) ← simpLocalDecl mvarId fvarId ctx {} (← mvarId.withContext <| mkDischarge?) (mayCloseGoal := false) | unreachable!
    return mvarId'

/--
Split an `if-then-else` in the goal target.
If `useNewSemantics` is `true`, the flag `backward.split` is ignored.
-/
def splitIfTarget? (mvarId : MVarId) (hName? : Option Name := none) (useNewSemantics := false) : MetaM (Option (ByCasesSubgoal × ByCasesSubgoal)) := commitWhenSome? do
  let some (s₁, s₂) ← splitIfAt? mvarId (← mvarId.getType) hName? | return none
  let mvarId₁ ← simpIfTarget s₁.mvarId (useNewSemantics := useNewSemantics)
  let mvarId₂ ← simpIfTarget s₂.mvarId (useNewSemantics := useNewSemantics)
  if s₁.mvarId == mvarId₁ && s₂.mvarId == mvarId₂ then
    trace[split.failure] "`split` tactic failed to simplify target using new hypotheses Goals:\n{mvarId₁}\n{mvarId₂}"
    return none
  else
    return some ({ s₁ with mvarId := mvarId₁ }, { s₂ with mvarId := mvarId₂ })

/--
Split an `if-then-else` in the hypothesis `fvarId`.
-/
def splitIfLocalDecl? (mvarId : MVarId) (fvarId : FVarId) (hName? : Option Name := none) : MetaM (Option (MVarId × MVarId)) := commitWhenSome? do
  mvarId.withContext do
    let some (s₁, s₂) ← splitIfAt? mvarId (← inferType (mkFVar fvarId)) hName? | return none
    let mvarId₁ ← simpIfLocalDecl s₁.mvarId fvarId
    let mvarId₂ ← simpIfLocalDecl s₂.mvarId fvarId
    if s₁.mvarId == mvarId₁ && s₂.mvarId == mvarId₂ then
      trace[split.failure] "`split` tactic failed to simplify target using new hypotheses Goals:\n{mvarId₁}\n{mvarId₂}"
      return none
    else
      return some (mvarId₁, mvarId₂)

builtin_initialize registerTraceClass `Meta.Tactic.splitIf

end Lean.Meta
