/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Elab.Tactic.Basic
public import Lean.Meta.Tactic.Simp.Types
import Lean.Meta.Tactic.Simp.Main
import Lean.Elab.Tactic.Do.ProofMode.MGoal
import Std.Tactic.Do -- Needed for use of `mleave` in quote
import Init.Data.Array.Mem

namespace Lean.Elab.Tactic.Do

open Lean Elab Tactic Meta ProofMode
open Std.Do

/--
If the target of `vc` looks like `(H ⊢ₛ T) args`, return `H args` and `T args`.
If the target looks like `ULift.down (T args)`, then this is likely a result of `mframe` and
`mleave`. In this case, the last decl in the local context of `vc` will look like
`ULift.down (H args)`. Then return `H args` and `T args`.

This means that both `H args` and `T args` have type `SPred []`.
-/
def getSPredGoalHypsAndTarget (type : Expr) : MetaM (Option (Level × Expr × Expr)) := do
  let args := type.getAppArgs
  if (type.isAppOf ``Std.Tactic.Do.MGoalEntails || type.isAppOf ``SPred.entails) && args.size > 2 then
    return (type.getAppFn.constLevels![0]!, (type.getArg! 1).beta args[3:], (type.getArg! 2).beta args[3:])
  let some decl := (← getLCtx).lastDecl | return none
  let hyps := decl.type.consumeMData
  let lvl := (getULiftDownLevel type <|> getULiftDownLevel hyps).getD .zero
  -- logWarning m!"getSPredGoalHypsAndTarget: {hyps} ⊢ₛ {type}"
  return (lvl, toAssertion lvl hyps, toAssertion lvl type)
where
  getULiftDownLevel (expr : Expr) : Option Level :=
    if expr.isAppOfArity ``ULift.down 2 then some expr.getAppFn.constLevels![0]! else none
  toAssertion (lvl : Level) (prop : Expr) : Expr :=
    if prop.isAppOfArity ``ULift.down 2 then
      prop.getArg! 1
    else
      SPred.mkPure lvl (TypeList.mkNil lvl) prop

structure InvariantUse where
  /-- Index 0 is the success condition, all the others are exception conditions. -/
  conditionIdx : Nat
  /-- The prefix expression of the call to `Cursor.mk`. -/
  cursorPrefix : Expr
  /-- The suffix expression of the call to `Cursor.mk`. -/
  cursorSuffix : Expr
  /-- The argument expressions of the `let mut` variables. -/
  letMuts : Array Expr
  letMutsTuple : Expr
  stateArgs : Array Expr

inductive ClassifyInvariantUseResult where
  | success (invariantUse : InvariantUse)
  | notAnInvariantUse
  | unknownInvariantUse

def classifyInvariantUse (assertion : Expr) (inv : MVarId) : ClassifyInvariantUseResult := Id.run do
  -- Looking through metadata here is important because of the name hints the proof mode leaves behind
  let assertion := assertion.consumeMData
  -- `assertion` looks like `?inv.2.2....1 payload args`. The number of `2`s is the condition index.
  -- The 0 index case is the success condition case and by far the most common.
  -- There we have `assertion = ?inv.1 payload args`.
  -- The chain of `.2.2...1` is normalized to nested applications of `Prod.fst` and `Prod.snd`:
  --   `@Prod.fst _ _ (@Prod.snd _ _ (@Prod.snd _ _ ... ?inv)) payload args`
  if !assertion.isAppOf ``Prod.fst then return .notAnInvariantUse
  let mut head := assertion.getArg! 2 -- indices 0 and 1 are type args
  let mut conditionIdx := 0
  while head != mkMVar inv do
    if !head.isAppOfArity ``Prod.snd 4 then return .notAnInvariantUse -- cannot classify as a use of the invariant!
    conditionIdx := conditionIdx + 1
    head := head.getRevArg! 1
  -- `head` is ?inv => Found the end of the chain.
  -- conditionIdx is the number of `Prod.snd`s in the chain, and ?inv really is the end of the chain.

  let args := assertion.getAppArgs
  -- logWarning m!"Found Prod.fst. Args: {args}"
  if args.size < 4 then return .notAnInvariantUse -- not an overapplication of `Prod.fst`. Types should prohibit this case
  let payload := args[3]!
  let stateArgs := args[4:]
  -- `stateArgs` can be non-empty when `σs` is non-empty.
  -- logWarning m!"Payload: {payload}"

  let_expr Prod.mk _ _ cursor letMutsTuple := payload | return .unknownInvariantUse -- NB: be conservative here
  let_expr List.Cursor.mk _α _l pref suff _prf := cursor | return .unknownInvariantUse -- dito
  let mut acc := letMutsTuple
  let mut letMuts := #[]
  while acc.isAppOfArity ``Prod.mk 4 do
    letMuts := letMuts.push (acc.getArg! 2)
    acc := acc.getArg! 3
  letMuts := letMuts.push acc
  return .success { conditionIdx, cursorPrefix := pref, cursorSuffix := suff, letMuts, letMutsTuple, stateArgs }

/--
Returns `some (ρ, σ)` if `letMutsTy` is of the form `Prod (Option ρ) σ` and every VC in `vcs`
uses the `Option ρ` component according to early return semantics.
* `ρ` is the type of early return (`Unit` in case of `break`)
* `σ` is an `n`-ary `Prod`, carrying the current value of the `let mut` variables.
  NB: When `n=0`, we have `Prod (Option ρ) PUnit` rather than `Option ρ`.
-/
def hasEarlyReturn (vcs : Array MVarId) (inv : MVarId) (letMutsTy : Expr) : MetaM (Option (Expr × Expr)) := do
  if !(letMutsTy.isAppOf ``Prod) || letMutsTy.getAppNumArgs < 2 then return none
  let_expr Option ρ := letMutsTy.getArg! 0 | return none
  let σ := letMutsTy.getArg! 1

  -- The predicate on `letMutsTy` above is not sufficient; after all the user might just have
  -- introduced `let mut ret : Option α` and not use this variable according to "early return
  -- semantics", meaning that *if* `ret = some r` for some `r : ρ`, then the loop body returns
  -- `ForInStep.done (ret, ...)`. This is a property upheld by the `do` elaborator.
  --
  -- At this point, `mvcgen` has already run, so we do not see the syntax of the original loop body.
  -- However, we know that loop invariant lemmas such as `Spec.forIn_list` require that the
  -- invariant holds at `suffix = []` whenever the loop body returns `ForInStep.done`.
  -- Therefore, a sufficient condition for early return depends on whether all the VCs conform to
  -- the property:
  --
  -- > For any use of `?inv` of the form `?inv.fst (cursor, ⟨ret, ...⟩)` it is provable that either
  -- > `ret = none` or `cursor.suffix = []`.
  --
  -- Examples of VC goal types that uphold the property:
  -- * `(Prod.fst ?inv ({ «prefix» := [], suffix := l, property := ⋯ }, ⟨none, PUnit.unit⟩)).down`
  --   because `ret=none`
  -- * `(Prod.fst ?inv ({ «prefix» := pref✝ ++ [cur✝], suffix := suff✝, property := ⋯ }, ⟨none, PUnit.unit⟩)).down`
  --   because `ret=none`
  -- * `(Prod.fst ?inv ({ «prefix» := l, suffix := [], property := ⋯ }, ⟨some true, PUnit.unit⟩)).down`
  --   because `suffix = []`
  -- Example of a VC not fulfilling the property:
  -- * `(Prod.fst ?inv ({ «prefix» := pref✝ ++ [cur✝], suffix := suff✝, property := ⋯ }, ⟨some cur✝, ()⟩)).down`
  --   because `ret = some _` and `suffix = suff✝` and `suff✝` has instances other than `[]`.
  -- And similarly for unsimplified entailment `_ ⊢ₛ Prod.fst ?inv (cursor, ⟨some r, ...⟩)`:
  -- * `_ ⊢ₛ Prod.fst ?inv ({ «prefix» := pref✝ ++ [cur✝], suffix := suff✝, property := ⋯ }, ⟨some cur✝, ()⟩)`
  --   because `ret = some _` and `suffix = suff✝` and `suff✝` has instances other than `[]`.
  --
  -- Hence we check all VCs for the property above.

  for vc in vcs do
    -- logWarning m!"Looking at {vc}."
    let type ← Expr.consumeMData <$> instantiateMVars (← vc.getType)
    let some (_, _, spredTarget) ← vc.withContext <| getSPredGoalHypsAndTarget type | continue
    -- logWarning m!"Found spredTarget: {spredTarget}"
    match classifyInvariantUse spredTarget inv with
    | .notAnInvariantUse => continue
    | .unknownInvariantUse => return none -- conservative
    | .success invariantUse =>
    -- logWarning m!"Invariant use: {invariantUse.letMuts}"
    -- The following check could be smarter. Essentially it tries to construct a proof that
    -- `suff = []` or `acc = (none, _)` and returns `none` upon failure.
    -- NB: There always is at least one `invariantUse.letMuts`.
    if !invariantUse.cursorSuffix.isAppOf ``List.nil && !invariantUse.letMuts[0]!.isAppOf ``Option.none then
      -- logWarning m!"No early return! Not a `List.nil`: {invariantUse.cursorSuffix} and not an `Option.none`: {invariantUse.letMuts[0]!}"
      return none

  return (ρ, σ)

def collectFVarsToRevert (e : Expr)(dontRevert : FVarId → Bool) : MetaM (Array Expr) := do
  let mut xs := (collectFVars {} e).fvarIds |>.filter (not ∘ dontRevert) |>.map mkFVar
  repeat do
    let new ← collectForwardDeps xs false
    let new := new.filter (not <| dontRevert ·.fvarId!)
    if new.size == xs.size then xs := new; break
    let types ← new.mapM inferType
    let forbidden := .ofArray new
    let s := (types.foldl collectFVars {visitedExpr := forbidden}).fvarIds |>.filter (not ∘ dontRevert)
    xs := new ++ s.map mkFVar
    if s.isEmpty then break -- no need for another iteration; collectForwardDeps is idempotent
  return xs

/-- Largely lifted from `Lean.MetavarContext.MkBinding.mkAuxMVarType`. -/
def revertFVarsInTypeExcept (e : Expr) (dontRevert : FVarId → Bool) : MetaM Expr := do
  let xs ← collectFVarsToRevert e dontRevert
  let lctx ← getLCtx
  let_expr c@SPred _σs := (← inferType e) | return e
  let lvl := c.constLevels![0]!
  -- logWarning m!"Reverting {xs} in {e}, {lvl}"
  let e ← xs.size.foldRevM (init := e.abstract xs) fun i _ e => do
    let x := xs[i]
    match lctx.getFVar! x with
    | LocalDecl.cdecl _ _ n type bi _ =>
      let type := type.headBeta
      let type := type.abstractRange i xs
      return mkApp3 (mkConst ``SPred.forall [← getLevel type, lvl]) type (TypeList.mkNil lvl) (Lean.mkLambda n bi type e)
    | LocalDecl.ldecl (nondep := true) _ _ n type _ _ =>
      let type := type.headBeta
      let type := type.abstractRange i xs
      return mkApp3 (mkConst ``SPred.forall [← getLevel type, lvl]) type (TypeList.mkNil lvl) (Lean.mkLambda n .default type e)
    | LocalDecl.ldecl (nondep := false) _ _ n type value _ =>
      if e.hasLooseBVar 0 then
        let type := type.headBeta
        let type := type.abstractRange i xs
        let value := value.abstractRange i xs
        return mkLet n type value e false
      else
        return e.lowerLooseBVars 1 1
  return e

structure SuccessPoint where
  /-- The level of the `SPred` state tuple. -/
  lvl : Level
  /-- An `SPred` like `⌜xs.prefix = []⌝` or `⌜xs.suffix = []⌝`. -/
  cursorPred : Expr
  /-- An arbitrary `SPred` on `letMuts`. -/
  letMutsPred : Expr

def SPredNil.mkAnd (lvl : Level) (lhs rhs : Expr) : Expr :=
  mkApp3 (mkConst ``SPred.and [lvl]) (TypeList.mkNil lvl) lhs rhs

def SPredNil.mkOr (lvl : Level) (lhs rhs : Expr) : Expr :=
  mkApp3 (mkConst ``SPred.or [lvl]) (TypeList.mkNil lvl) lhs rhs

def SuccessPoint.clause (p : SuccessPoint) : Expr :=
  SPredNil.mkAnd p.lvl p.cursorPred p.letMutsPred

/-- The last syntactic element of a `FailureCond`. -/
inductive ExceptCondsDefault where
  /-- `PUnit.unit`. This means we can suggest `post⟨...⟩`. -/
  | punit
  /-- `ExceptConds.false`. This means we can suggest `⇓ _ => _`. -/
  | false
  /-- `ExceptConds.true`. This means we can suggest `⇓? _ => _`. -/
  | true
  /-- Something else. This means we can only suggest `by exact ⟨..., e⟩`. -/
  | other (e : Expr)

/--
If `points[n]` is `fun e => assertion`, then the invariant should look like
```
post⟨... success ..., ... n except conds ..., fun e => assertion, ... other stuff ...⟩
```
So each entry describes a non-`False` exception condition.

When the default is not defeq to `ExceptConds.false`, we use it as the default.
-/
structure FailureCondHints where
  points : Array Expr := #[]
  default : ExceptCondsDefault := .punit

/-- Look at how `inv` is used in the `vcs` and collect hints about how `inv` should be instantiated.
In case it succeeds, there will be
* A `SuccessPoint` for the `xs.prefix = []` case
* A `SuccessPoint` for all the `xs.suffix = []` case (control flow splits can introduce multiple
  relevant VCs)
* A `FailureCondHints` with the default exception condition (i.e., `FailureConds.false`, `()` or
  something else?) and the non-defaulted exception conditions.
-/
def collectInvariantHints (vcs : Array MVarId) (inv : MVarId) (xs : Expr) (letMuts : Expr) : MetaM (Option (SuccessPoint × SuccessPoint × FailureCondHints)) := do
  let lctx ← getLCtx -- this is the local context of `inv` extended by `xs` and `letMuts`
  let mut prefixPoint? : Option SuccessPoint := none
  let mut suffixPoint? : Option SuccessPoint := none
  let mut failureConds : FailureCondHints := {}
  for vc in vcs do
    -- logWarning m!"Looking at {vc}."
    let target ← Expr.consumeMData <$> instantiateMVars (← vc.getType)
    if let some (lvl, spredHyps, spredTarget) ← vc.withContext <| getSPredGoalHypsAndTarget target then
      let mkPure p := SPred.mkPure lvl (TypeList.mkNil lvl) p
      -- vc.withContext <| logWarning m!"collectPoint: {spredHyps} ⊢ₛ {spredTarget}"
      if let .success invariantUse := classifyInvariantUse spredTarget inv then
        -- This is the `xs.prefix = []` case.
        -- vc.withContext <| logWarning m!"Invariant use: {invariantUse.letMutsTuple}"
        if invariantUse.conditionIdx != 0 then continue -- concerns the success conditions
        if invariantUse.cursorPrefix.isAppOf ``List.nil then
          -- eqNil := `(xs.prefix = [])
          let xsPrefix ← mkProjection xs `prefix
          let eqNil ← mkEq xsPrefix invariantUse.cursorPrefix
          -- eqLetMuts := `(letMuts = $(invariantUse.letMutsTuple))
          let eqLetMuts ← mkPure <$> mkEq letMuts invariantUse.letMutsTuple
          -- logWarning m!"Found prefix point: {eqLetMuts}"
          prefixPoint? := some { lvl, cursorPred := mkPure eqNil, letMutsPred := eqLetMuts }
      if let .success invariantUse := classifyInvariantUse spredHyps inv then
        -- This is a `xs.suffix = []` case.
        -- vc.withContext <| logWarning m!"Found spredHyp: {spredHyps}"
        if invariantUse.conditionIdx != 0 then continue -- concerns the success conditions
        if invariantUse.cursorSuffix.isAppOf ``List.nil && invariantUse.letMutsTuple.isFVar then
          let xsPrefix ← mkProjection xs `suffix
          let eqNil ← mkEq xsPrefix invariantUse.cursorSuffix
          let dontRevert fvarId := fvarId == invariantUse.letMutsTuple.fvarId! || lctx.contains fvarId
          let eqLetMuts ← vc.withContext <| revertFVarsInTypeExcept spredTarget dontRevert
          let eqLetMuts := eqLetMuts.replaceFVar invariantUse.letMutsTuple letMuts
          -- logWarning m!"Reverted to {eqLetMuts}"
          if let some suffixPoint := suffixPoint? then
            suffixPoint? := some { suffixPoint with letMutsPred := SPredNil.mkAnd lvl suffixPoint.letMutsPred eqLetMuts }
          else
            suffixPoint? := some { lvl, cursorPred := mkPure eqNil, letMutsPred := eqLetMuts }
    if let some (_ps, lhs, rhs) := target.app3? ``ExceptConds.entails then
      -- This is a exception condition case.
      -- logWarning m!"Found ExceptConds.entails: {lhs}, {rhs}"
      -- We are targeting `Prod.snd ?inv ⊢ₑ blah` specifically
      unless lhs.isAppOfArity ``Prod.snd 3 && lhs.getArg! 2 == mkMVar inv do continue
      let mut n := 0
      let mut conds := rhs
      let mut points := #[]
      while conds.isAppOfArity ``Prod.mk 4 do
        points := points.push (conds.getArg! 2)
        n := n + 1
        conds := conds.getArg! 3
      if points.size > failureConds.points.size then
        -- Just overwrite the existing entry. Computing a join here is overkill for the few cases
        -- where this is going to be used.
        failureConds := { failureConds with points := points }
        if conds.isConstOf ``PUnit.unit then
          failureConds := { failureConds with default := .punit }
        else if conds.isAppOfArity ``ExceptConds.false 1 then
          failureConds := { failureConds with default := .false }
        else if conds.isAppOfArity ``ExceptConds.true 1 then
          failureConds := { failureConds with default := .true }
        else
          failureConds := { failureConds with default := .other conds }
      -- vc.withContext <| logWarning m!"Found failure conds: {failureConds.points.toList}"
  return (·, ·, ·) <$> prefixPoint? <*> suffixPoint? <*> pure failureConds

def duplicateMVar (m : MVarId) : MetaM MVarId := do
  let d ← m.getDecl
  let e ← mkFreshExprMVarAt d.lctx d.localInstances d.type d.kind d.userName d.numScopeArgs
  return e.mvarId!

/-- Remove the macro scopes introduced by quote expansion from the syntax. -/
def eraseQuoteMacroScopesFromSyntax : Syntax → Syntax
  | Syntax.ident info rawVal val preresolved =>
    if rawVal.contains '@' then
      -- This was an inaccessible name in the proof state. Its raw val looks like
      --   "acc._@.external:file:///.../tests/lean/run/mvcgenInvariantsSuggestions.lean.2049968788._hygCtx._hyg.56"
      -- Keep the macro scopes!
      Syntax.ident info rawVal val preresolved
    else
      -- This was one of the names made inaccessible by quote expansion. Its raw val looks like
      --   "xs"
      -- Erase the macro scopes.
      Syntax.ident info rawVal val.eraseMacroScopes preresolved
  | Syntax.node info kind args =>
    Syntax.node info kind (args.map eraseQuoteMacroScopesFromSyntax)
  | Syntax.atom info val => Syntax.atom info val
  | Syntax.missing => Syntax.missing

/-- Remove the macro scopes introduced by quote expansion from the syntax. -/
def eraseQuoteMacroScopesFromTSyntax (syn : TSyntax name) : TSyntax name :=
  ⟨eraseQuoteMacroScopesFromSyntax syn.raw⟩

/--
A simple ad-hoc version of `SPred.Tactic.IsPure`, but without producing a proof and without
involving the type class machinery.
Example: `spred(∀x, ⌜a⌝ → let y := v; ⌜b⌝ ∧ ⌜c⌝ ∨ ⌜d⌝)` becomes `⌜∀x, a → let y := v; b ∧ c ∨ d⌝`.
-/
partial def tryHoistPure (e : Expr) : Expr :=
  match go e with
  | none => e
  | some (lvl, e) => SPred.mkPure lvl (TypeList.mkNil lvl) e
where
  go (e : Expr) : Option (Level × Expr) := do
    if e.isAppOfArity ``SPred.pure 2 then
      return (e.getAppFn.constLevels![0]!, e.getArg! 1)
    if let some (_, lhs, rhs) := e.app3? ``SPred.and then
      let (_, lhs) ← go lhs
      let (lvl, rhs) ← go rhs
      return (lvl, mkAnd lhs rhs)
    if let some (_, lhs, rhs) := e.app3? ``SPred.or then
      let (_, lhs) ← go lhs
      let (lvl, rhs) ← go rhs
      return (lvl, mkOr lhs rhs)
    if let some (_, _, .lam n ty body bi) := e.app3? ``SPred.forall then
      let (lvl, body) ← go body
      return (lvl, mkForall n bi ty body)
    if let .letE n ty val body nondep := e then
      let (lvl, body) ← go body
      return (lvl, .letE n ty val body nondep)
    failure

/--
Based on how a given metavariable `inv` binding a `Std.Do.Invariant` is used in the `vcs`, suggest
an initial assignment for `inv` to fill in for the user.
-/
public def suggestInvariant (vcs : Array MVarId) (inv : MVarId) : TacticM Term := do
  -- We only synthesize suggestions for invariant subgoals
  let invType ← instantiateMVars (← inv.getType)
  let_expr c@Std.Do.Invariant α l letMutsTy _ps := invType
    | throwError "Expected invariant type, got {invType}"
  let us := c.constLevels!.take 1 -- This is the list of universe params for `List.Cursor`. It only
                                  -- takes the level `u₁` for `α` in the type of `Invariant`, so
                                  -- we drop the rest (i.e., `u₂` for `β`).

  -- Simplify the VCs a bit using `mleave`. Makes the job of the analysis below simpler.
  let vcs ← vcs.flatMapM fun vc =>
    try
      (·.toArray) <$> evalTacticAt (← `(tactic| mleave)) (← duplicateMVar vc)
    catch _e =>
      -- logWarning m!"Failed to simplify {vc}: {_e.toMessageData}"
      pure #[vc]

  inv.withContext do
  -- Build the success points into self-contained lambdas, to be beta reduced below.
  let suggestion? ←
    withLocalDeclD `xs (mkApp2 (mkConst ``List.Cursor us) α l) fun xs =>
    withLocalDeclD `letMuts letMutsTy fun letMuts => do
    let some (prefixPoint, suffixPoint, failureConds) ← collectInvariantHints vcs inv xs letMuts | return none
    let pred := SPredNil.mkOr prefixPoint.lvl prefixPoint.clause suffixPoint.clause
    let success ← mkLambdaFVars #[xs, letMuts] (tryHoistPure pred)
    let onReturn ← mkLambdaFVars #[letMuts] (tryHoistPure suffixPoint.letMutsPred)
    return some (success, onReturn, failureConds)

  -- Quotes introduce macro scopes to any binders. `eraseQuoteMacroScopesFromTSyntax` removes just
  -- those, and will not remove any inaccessible markers stemming from inaccessible free variables
  -- in the proof state.
  eraseQuoteMacroScopesFromTSyntax <$> do
  --
  -- Finally, build the syntax for the suggestion. It's a giant configuration space mess, because
  -- 1. Generally want to suggest something using `⇓ ⟨xs, letMuts⟩ => ...`, i.e. `PostCond.noThrow`.
  -- 2. However, on early return we want to suggest something using `Invariant.withEarlyReturnNewDo`.
  -- 3. When there are non-`False` failure conditions, we cannot suggest `⇓ ⟨xs, letMuts⟩ => ...`.
  --    We might be able to suggest `⇓? ⟨xs, letMuts⟩ => ...` (`True` failure condition),
  --    or `post⟨...⟩` (more than 0 failure handlers, but ending in `PUnit.unit`), and fall back to
  --    `by exact ⟨...⟩` (not ending in `PUnit.unit`).
  -- 4. Similarly for the `onExcept` argument of `Invariant.withEarlyReturnNewDo`.
  -- Hence the spaghetti code.
  --
  if let some (ρ, σ) ← hasEarlyReturn vcs inv letMutsTy then
    -- logWarning m!"Found early return for {inv}!"
    -- Suggest an invariant using `Invariant.withEarlyReturnNewDo`.
    if let some (success, onReturn, failureConds) := suggestion? then
      -- First construct `onContinue` and `onReturn` clause and simplify them according to the
      -- definition of `Invariant.withEarlyReturnNewDo`.
      let (onContinue, onReturn) ← withLocalDeclD `xs (mkApp2 (mkConst ``List.Cursor us) α l) fun xs =>
        withLocalDeclD `r ρ fun r =>
        withLocalDeclD `letMuts σ fun letMuts => do
        let onContinue := success.beta #[xs, ← mkAppM ``Prod.mk #[← mkNone ρ, letMuts]]
        let onReturn := onReturn.beta #[← mkAppM ``Prod.mk #[← mkSome ρ r, letMuts]]
        let ctx ← Simp.mkContext
          (config := {})
          (simpTheorems := #[(← Meta.getSimpTheorems)])
          (congrTheorems := (← Meta.getSimpCongrTheorems))
        let simprocs ← ({} : Simp.SimprocsArray).add `reduceCtorEq false
        let (res1, _) ← Lean.Meta.simp onContinue ctx simprocs
        let (res2, _) ← Lean.Meta.simp onReturn ctx simprocs
        return (← Lean.PrettyPrinter.delab res1.expr, ← Lean.PrettyPrinter.delab res2.expr)
      -- Now the configuration mess.
      if failureConds.points.isEmpty then
        match failureConds.default with
        | .false | .punit =>
          `(Invariant.withEarlyReturnNewDo (onReturn := fun r letMuts => $onReturn) (onContinue := fun xs letMuts => $onContinue))
        -- we handle the following two cases here rather than through
        -- `postCondWithMultipleConditions` below because that would insert a superfluous `by exact _`.
        | .true =>
          `(Invariant.withEarlyReturnNewDo (onReturn := fun r letMuts => $onReturn) (onContinue := fun xs letMuts => $onContinue (onExcept := ExceptConds.true)))
        | .other e =>
          `(Invariant.withEarlyReturnNewDo (onReturn := fun r letMuts => $onReturn) (onContinue := fun xs letMuts => $onContinue (onExcept := $(← Lean.PrettyPrinter.delab e))))
      else -- need the postcondition long form as `onExcept` arg
        let mut terms : Array Term := #[]
        for point in failureConds.points do
          terms := terms.push (← Lean.PrettyPrinter.delab point)
        let onExcept ← postCondWithMultipleConditions terms failureConds.default
        `(Invariant.withEarlyReturnNewDo (onReturn := fun r letMuts => $onReturn) (onContinue := fun xs letMuts => $onContinue) (onExcept := $onExcept))
    else -- No suggestion. Just fill in `_`.
      `(Invariant.withEarlyReturnNewDo (onReturn := fun r letMuts => _) (onContinue := fun xs letMuts => _))
  else if let some (success, _, failureConds) := suggestion? then
    -- No early return, but we do have a suggestion.
    withLocalDeclD `xs (mkApp2 (mkConst ``List.Cursor us) α l) fun xs =>
    withLocalDeclD `letMuts letMutsTy fun letMuts => do
    let successBody ← Lean.PrettyPrinter.delab (success.beta #[xs, letMuts])
    -- Configuration mess
    if failureConds.points.isEmpty && not (failureConds.default matches .other _) then
      if (failureConds.default matches .true) then
        `(⇓? ⟨xs, letMuts⟩ => $successBody)
      else
        `(⇓ ⟨xs, letMuts⟩ => $successBody)
    else -- need the long form
      let mut terms : Array Term := #[← `(fun ⟨xs, letMuts⟩ => $successBody)]
      for point in failureConds.points do
        terms := terms.push (← Lean.PrettyPrinter.delab point)
      postCondWithMultipleConditions terms failureConds.default
  else
    -- No early return and no suggestion. Just suggest _something_.
    -- `PostCond.noThrow` is the most common case.
    `(⇓ ⟨xs, letMuts⟩ => _)
where
  postCondWithMultipleConditions (handlers : Array Term) (default : ExceptCondsDefault) : MetaM Term := do
    let handlers := Syntax.TSepArray.ofElems (sep := ",") handlers
    match default with
    | .punit => `(post⟨$handlers,*⟩)
    -- See the comment in `post⟨_⟩` syntax for why we emit `by exact` here.
    | .false => `(by exact ⟨$handlers,*, ExceptConds.false⟩)
    | .true => `(by exact ⟨$handlers,*, ExceptConds.true⟩)
    | .other e => `(by exact ⟨$handlers,*, $(← Lean.PrettyPrinter.delab e)⟩)
