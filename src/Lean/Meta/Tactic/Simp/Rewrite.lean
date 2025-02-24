/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.ACLt
import Lean.Meta.Match.MatchEqsExt
import Lean.Meta.AppBuilder
import Lean.Meta.SynthInstance
import Lean.Meta.Tactic.Util
import Lean.Meta.Tactic.UnifyEq
import Lean.Meta.Tactic.Simp.Types
import Lean.Meta.Tactic.Simp.Arith
import Lean.Meta.Tactic.Simp.Simproc
import Lean.Meta.Tactic.Simp.Attr
import Lean.Meta.BinderNameHint

namespace Lean.Meta.Simp

/--
Helper type for implementing `discharge?'`
-/
inductive DischargeResult where
  | proved
  | notProved
  | maxDepth
  | failedAssign
  deriving DecidableEq

/--
Wrapper for invoking `discharge?` method. It checks for maximum discharge depth, create trace nodes, and ensure
the generated proof was successfully assigned to `x`.
-/
def discharge?' (thmId : Origin) (x : Expr) (type : Expr) : SimpM Bool := do
  let r : DischargeResult ← withTraceNode `Meta.Tactic.simp.discharge (fun
      | .ok .proved       => return m!"{← ppOrigin thmId} discharge {checkEmoji}{indentExpr type}"
      | .ok .notProved    => return m!"{← ppOrigin thmId} discharge {crossEmoji}{indentExpr type}"
      | .ok .maxDepth     => return m!"{← ppOrigin thmId} discharge {crossEmoji} max depth{indentExpr type}"
      | .ok .failedAssign => return m!"{← ppOrigin thmId} discharge {crossEmoji} failed to assign proof{indentExpr type}"
      | .error err        => return m!"{← ppOrigin thmId} discharge {crossEmoji}{indentExpr type}{indentD err.toMessageData}") do
    let ctx ← getContext
    if ctx.dischargeDepth >= ctx.maxDischargeDepth then
      return .maxDepth
    else withIncDischargeDepth do
      -- We save the state, so that `UsedTheorems` does not accumulate
      -- `simp` lemmas used during unsuccessful discharging.
      -- We use `withPreservedCache` to ensure the cache is restored after `discharge?`
      let usedTheorems := (← get).usedTheorems
      match (← withPreservedCache <| (← getMethods).discharge? type) with
      | some proof =>
        unless (← isDefEq x proof) do
          modify fun s => { s with usedTheorems }
          return .failedAssign
        return .proved
      | none =>
        modify fun s => { s with usedTheorems }
        return .notProved
  return r = .proved

def synthesizeArgs (thmId : Origin) (bis : Array BinderInfo) (xs : Array Expr) : SimpM Bool := do
  let skipAssignedInstances := tactic.skipAssignedInstances.get (← getOptions)
  for x in xs, bi in bis do
    let type ← inferType x
    -- We use the flag `tactic.skipAssignedInstances` for backward compatibility.
    -- See comment below.
    if !skipAssignedInstances && bi.isInstImplicit then
      unless (← synthesizeInstance x type) do
        return false
    /-
    We used to invoke `synthesizeInstance` for every instance implicit argument,
    to ensure the synthesized instance was definitionally equal to the one in
    the term, but it turned out to be to inconvenient in practice. Here is an
    example:
    ```
    theorem dec_and (p q : Prop) [Decidable (p ∧ q)] [Decidable p] [Decidable q] : decide (p ∧ q) = (p && q) := by
      by_cases p <;> by_cases q <;> simp [*]

    theorem dec_not (p : Prop) [Decidable (¬p)] [Decidable p] : decide (¬p) = !p := by
      by_cases p <;> simp [*]

    example [Decidable u] [Decidable v] : decide (u ∧ (v → False)) = (decide u && !decide v) := by
      simp only [imp_false]
      simp only [dec_and]
      simp only [dec_not]
    ```
    -/
    if (← instantiateMVars x).isMVar then
      -- A hypothesis can be both a type class instance as well as a proposition,
      -- in that case we try both TC synthesis and the discharger
      -- (because we don't know whether the argument was originally explicit or instance-implicit).
      if (← isClass? type).isSome then
        if (← synthesizeInstance x type) then
          continue
      if (← isProp type) then
        unless (← discharge?' thmId x type) do
          return false
  return true
where
  synthesizeInstance (x type : Expr) : SimpM Bool := do
    match (← trySynthInstance type) with
    | LOption.some val =>
      if (← withReducibleAndInstances <| isDefEq x val) then
        return true
      else
        trace[Meta.Tactic.simp.discharge] "{← ppOrigin thmId}, failed to assign instance{indentExpr type}\nsythesized value{indentExpr val}\nis not definitionally equal to{indentExpr x}"
        return false
    | _ =>
      trace[Meta.Tactic.simp.discharge] "{← ppOrigin thmId}, failed to synthesize instance{indentExpr type}"
      return false

private def useImplicitDefEqProof (thm : SimpTheorem) : SimpM Bool := do
  if thm.rfl then
    return (← getConfig).implicitDefEqProofs
  else
    return false

private def tryTheoremCore (lhs : Expr) (xs : Array Expr) (bis : Array BinderInfo) (val : Expr) (type : Expr) (e : Expr) (thm : SimpTheorem) (numExtraArgs : Nat) : SimpM (Option Result) := do
  recordTriedSimpTheorem thm.origin
  let rec go (e : Expr) : SimpM (Option Result) := do
    if (← withSimpMetaConfig <| isDefEq lhs e) then
      unless (← synthesizeArgs thm.origin bis xs) do
        return none
      let proof? ← if (← useImplicitDefEqProof thm) then
        pure none
      else
        let proof ← instantiateMVars (mkAppN val xs)
        if (← hasAssignableMVar proof) then
          trace[Meta.Tactic.simp.rewrite] "{← ppSimpTheorem thm}, has unassigned metavariables after unification"
          return none
        pure <| some proof
      let rhs := (← instantiateMVars type).appArg!
      /-
      We used to use `e == rhs` in the following test.
      However, it include unnecessary proof steps when `e` and `rhs`
      are equal after metavariables are instantiated.
      We are hoping the following `instantiateMVars` should not be too expensive since
      we seldom have assigned metavariables in goals.
      -/
      if (← instantiateMVars e) == rhs then
        return none
      if thm.perm then
        /-
        We use `.reduceSimpleOnly` because this is how we indexed the discrimination tree.
        See issue #1815
        -/
        if !(← acLt rhs e .reduceSimpleOnly) then
          trace[Meta.Tactic.simp.rewrite] "{← ppSimpTheorem thm}, perm rejected {e} ==> {rhs}"
          return none
      trace[Meta.Tactic.simp.rewrite] "{← ppSimpTheorem thm}:{indentExpr e}\n==>{indentExpr rhs}"
      let rhs ← if type.hasBinderNameHint then rhs.resolveBinderNameHint else pure rhs
      recordSimpTheorem thm.origin
      return some { expr := rhs, proof? }
    else
      unless lhs.isMVar do
        -- We do not report unification failures when `lhs` is a metavariable
        -- Example: `x = ()`
        -- TODO: reconsider if we want thms such as `(x : Unit) → x = ()`
        trace[Meta.Tactic.simp.unify] "{← ppSimpTheorem thm}, failed to unify{indentExpr lhs}\nwith{indentExpr e}"
      return none
  /- Check whether we need something more sophisticated here.
     This simple approach was good enough for Mathlib 3 -/
  let mut extraArgs := #[]
  let mut e := e
  for _ in [:numExtraArgs] do
    extraArgs := extraArgs.push e.appArg!
    e := e.appFn!
  extraArgs := extraArgs.reverse
  match (← go e) with
  | none => return none
  | some r =>
    if (← hasAssignableMVar r.expr) then
      trace[Meta.Tactic.simp.rewrite] "{← ppSimpTheorem thm}, resulting expression has unassigned metavariables"
      return none
    r.addExtraArgs extraArgs

def tryTheoremWithExtraArgs? (e : Expr) (thm : SimpTheorem) (numExtraArgs : Nat) : SimpM (Option Result) :=
  withNewMCtxDepth do
    let val  ← thm.getValue
    let type ← inferType val
    let (xs, bis, type) ← forallMetaTelescopeReducing type
    let type ← whnf (← instantiateMVars type)
    let lhs := type.appFn!.appArg!
    tryTheoremCore lhs xs bis val type e thm numExtraArgs

def tryTheorem? (e : Expr) (thm : SimpTheorem) : SimpM (Option Result) := do
  withNewMCtxDepth do
    let val  ← thm.getValue
    let type ← inferType val
    let (xs, bis, type) ← forallMetaTelescopeReducing type
    let type ← whnf (← instantiateMVars type)
    let lhs := type.appFn!.appArg!
    match (← tryTheoremCore lhs xs bis val type e thm 0) with
    | some result => return some result
    | none =>
      let lhsNumArgs := lhs.getAppNumArgs
      let eNumArgs   := e.getAppNumArgs
      if eNumArgs > lhsNumArgs then
        tryTheoremCore lhs xs bis val type e thm (eNumArgs - lhsNumArgs)
      else
        return none

/--
Remark: the parameter tag is used for creating trace messages. It is irrelevant otherwise.
-/
def rewrite? (e : Expr) (s : SimpTheoremTree) (erased : PHashSet Origin) (tag : String) (rflOnly : Bool) : SimpM (Option Result) := do
  if (← getConfig).index then
    rewriteUsingIndex?
  else
    rewriteNoIndex?
where
  /-- For `(← getConfig).index := true`, use discrimination tree structure when collecting `simp` theorem candidates. -/
  rewriteUsingIndex? : SimpM (Option Result) := do
    let candidates ← withSimpIndexConfig <| s.getMatchWithExtra e
    if candidates.isEmpty then
      trace[Debug.Meta.Tactic.simp] "no theorems found for {tag}-rewriting {e}"
      return none
    else
      let candidates := candidates.insertionSort fun e₁ e₂ => e₁.1.priority > e₂.1.priority
      for (thm, numExtraArgs) in candidates do
        unless inErasedSet thm || (rflOnly && !thm.rfl) do
          if let some result ← tryTheoremWithExtraArgs? e thm numExtraArgs then
            trace[Debug.Meta.Tactic.simp] "rewrite result {e} => {result.expr}"
            return some result
      return none

  /--
  For `(← getConfig).index := false`, Lean 3 style `simp` theorem retrieval.
  Only the root symbol is taken into account. Most of the structure of the discrimination tree is ignored.
  -/
  rewriteNoIndex? : SimpM (Option Result) := do
    let (candidates, numArgs) ← withSimpIndexConfig <| s.getMatchLiberal e
    if candidates.isEmpty then
      trace[Debug.Meta.Tactic.simp] "no theorems found for {tag}-rewriting {e}"
      return none
    else
      let candidates := candidates.insertionSort fun e₁ e₂ => e₁.priority > e₂.priority
      for thm in candidates do
        unless inErasedSet thm || (rflOnly && !thm.rfl) do
          let result? ← withNewMCtxDepth do
            let val  ← thm.getValue
            let type ← inferType val
            let (xs, bis, type) ← forallMetaTelescopeReducing type
            let type ← whnf (← instantiateMVars type)
            let lhs := type.appFn!.appArg!
            let lhsNumArgs := lhs.getAppNumArgs
            tryTheoremCore lhs xs bis val type e thm (numArgs - lhsNumArgs)
          if let some result := result? then
            trace[Debug.Meta.Tactic.simp] "rewrite result {e} => {result.expr}"
            diagnoseWhenNoIndex thm
            return some result
    return none

  diagnoseWhenNoIndex (thm : SimpTheorem) : SimpM Unit := do
    if (← isDiagnosticsEnabled) then
      let candidates ← withSimpIndexConfig <| s.getMatchWithExtra e
      for (candidate, _) in candidates do
        if unsafe ptrEq thm candidate then
          return ()
      -- `thm` would not have been applied if `index := true`
      recordTheoremWithBadKeys thm

  inErasedSet (thm : SimpTheorem) : Bool :=
    erased.contains thm.origin

@[inline] def simpUsingDecide : Simproc := fun e => do
  unless (← getConfig).decide do
    return .continue
  if e.hasFVar || e.hasMVar || e.isTrue || e.isFalse then
    return .continue
  try
    let d ← mkDecide e
    let r ← withDefault <| whnf d
    if r.isConstOf ``true then
      return .done { expr := mkConst ``True, proof? := mkAppN (mkConst ``eq_true_of_decide) #[e, d.appArg!, (← mkEqRefl (mkConst ``true))] }
    else if r.isConstOf ``false then
      return .done { expr := mkConst ``False, proof? := mkAppN (mkConst ``eq_false_of_decide) #[e, d.appArg!, (← mkEqRefl (mkConst ``false))] }
    else
      return .continue
  catch _ =>
    return .continue

def simpArith (e : Expr) : SimpM Step := do
  unless (← getConfig).arith do
    return .continue
  if Arith.isLinearCnstr e then
    if let some (e', h) ← Arith.Nat.simpCnstr? e then
      return .visit { expr := e', proof? := h }
    else if let some (e', h) ← Arith.Int.simpRel? e then
      return .visit { expr := e', proof? := h }
    else if let some (e', h) ← Arith.Int.simpEq? e then
      return .visit { expr := e', proof? := h }
    else
      return .continue
  else if Arith.isLinearTerm e then
    if Arith.parentIsTarget (← getContext).parent? then
      -- We mark `cache := false` to ensure we do not miss simplifications.
      return .continue (some { expr := e, cache := false })
    else if let some (e', h) ← Arith.Nat.simpExpr? e then
      return .visit { expr := e', proof? := h }
    else if let some (e', h) ← Arith.Int.simpExpr? e then
      return .visit { expr := e', proof? := h }
    else
      return .continue
  else if Arith.isDvdCnstr e then
    if let some (e', h) ← Arith.Int.simpDvd? e then
      return .visit { expr := e', proof? := h }
    else
      return .continue
  else
    return .continue

/--
Given a match-application `e` with `MatcherInfo` `info`, return `some result`
if at least of one of the discriminants has been simplified.
-/
def simpMatchDiscrs? (info : MatcherInfo) (e : Expr) : SimpM (Option Result) := do
  let numArgs := e.getAppNumArgs
  if numArgs < info.arity then
    return none
  let prefixSize := info.numParams + 1 /- motive -/
  let n     := numArgs - prefixSize
  let f     := e.stripArgsN n
  let infos := (← getFunInfoNArgs f n).paramInfo
  let args  := e.getAppArgsN n
  let mut r : Result := { expr := f }
  let mut modified := false
  for i in [0 : info.numDiscrs] do
    let arg := args[i]!
    if i < infos.size && !infos[i]!.hasFwdDeps then
      let argNew ← simp arg
      if argNew.expr != arg then modified := true
      r ← mkCongr r argNew
    else if (← whnfD (← inferType r.expr)).isArrow then
      let argNew ← simp arg
      if argNew.expr != arg then modified := true
      r ← mkCongr r argNew
    else
      let argNew ← dsimp arg
      if argNew != arg then modified := true
      r ← mkCongrFun r argNew
  unless modified do
    return none
  for h : i in [info.numDiscrs : args.size] do
    let arg := args[i]
    r ← mkCongrFun r arg
  return some r

def simpMatchCore (matcherName : Name) (e : Expr) : SimpM Step := do
  for matchEq in (← Match.getEquationsFor matcherName).eqnNames do
    -- Try lemma
    match (← withReducible <| Simp.tryTheorem? e { origin := .decl matchEq, proof := mkConst matchEq, rfl := (← isRflTheorem matchEq) }) with
    | none   => pure ()
    | some r => return .visit r
  return .continue

def simpMatch : Simproc := fun e => do
  unless (← getConfig).iota do
    return .continue
  if let some e ← withSimpMetaConfig <| reduceRecMatcher? e then
    return .visit { expr := e }
  let .const declName _ := e.getAppFn
    | return .continue
  let some info ← getMatcherInfo? declName
    | return .continue
  if let some r ← simpMatchDiscrs? info e then
    return .visit r
  simpMatchCore declName e

def rewritePre (rflOnly := false) : Simproc := fun e => do
  for thms in (← getContext).simpTheorems do
    if let some r ← rewrite? e thms.pre thms.erased (tag := "pre") (rflOnly := rflOnly) then
      return .visit r
  return .continue

def rewritePost (rflOnly := false) : Simproc := fun e => do
  for thms in (← getContext).simpTheorems do
    if let some r ← rewrite? e thms.post thms.erased (tag := "post") (rflOnly := rflOnly) then
      return .visit r
  return .continue

def drewritePre : DSimproc := fun e => do
  for thms in (← getContext).simpTheorems do
    if let some r ← rewrite? e thms.pre thms.erased (tag := "dpre") (rflOnly := true) then
      return .visit r.expr
  return .continue

def drewritePost : DSimproc := fun e => do
  for thms in (← getContext).simpTheorems do
    if let some r ← rewrite? e thms.post thms.erased (tag := "dpost") (rflOnly := true) then
      return .visit r.expr
  return .continue

def dpreDefault (s : SimprocsArray) : DSimproc :=
  drewritePre >>
  userPreDSimprocs s

def dpostDefault (s : SimprocsArray) : DSimproc :=
  drewritePost >>
  userPostDSimprocs s

/--
Discharge procedure for the ground/symbolic evaluator.
-/
def dischargeGround (e : Expr) : SimpM (Option Expr) := do
  let r ← simp e
  if r.expr.isTrue then
    try
      return some (← mkOfEqTrue (← r.getProof))
    catch _ =>
      return none
  else
    return none

/--
Try to unfold ground term in the ground/symbolic evaluator.
-/
def sevalGround : Simproc := fun e => do
  -- `e` is not a ground term.
  unless !e.hasExprMVar && !e.hasFVar do return .continue
  -- Check whether `e` is a constant application
  let f := e.getAppFn
  let .const declName lvls := f | return .continue
  -- If declaration has been marked to not be unfolded, return none.
  let ctx ← getContext
  if ctx.simpTheorems.isErased (.decl declName) then return .continue
  -- Matcher applications should have been reduced before we get here.
  if (← isMatcher declName) then return .continue
  if let some eqns ← withDefault <| getEqnsFor? declName then
    -- `declName` has equation theorems associated with it.
    for eqn in eqns do
      -- TODO: cache SimpTheorem to avoid calls to `isRflTheorem`
      if let some result ← Simp.tryTheorem? e { origin := .decl eqn, proof := mkConst eqn, rfl := (← isRflTheorem eqn) } then
        trace[Meta.Tactic.simp.ground] "unfolded, {e} => {result.expr}"
        return .visit result
    return .continue
  -- `declName` does not have equation theorems associated with it.
  if e.isConst then
    -- We don't unfold constants that take arguments
    if let .forallE .. ← whnfD (← inferType e) then
      return .continue
  let info ← getConstInfo declName
  unless info.hasValue && info.levelParams.length == lvls.length do return .continue
  let fBody ← instantiateValueLevelParams info lvls
  let eNew := fBody.betaRev e.getAppRevArgs (useZeta := true)
  trace[Meta.Tactic.simp.ground] "delta, {e} => {eNew}"
  return .visit { expr := eNew }

partial def preSEval (s : SimprocsArray) : Simproc :=
  rewritePre >>
  simpMatch >>
  userPreSimprocs s

def postSEval (s : SimprocsArray) : Simproc :=
  rewritePost >>
  userPostSimprocs s >>
  sevalGround

def mkSEvalMethods : CoreM Methods := do
  let s ← getSEvalSimprocs
  return {
    pre        := preSEval #[s]
    post       := postSEval #[s]
    dpre       := dpreDefault #[s]
    dpost      := dpostDefault #[s]
    discharge? := dischargeGround
    wellBehavedDischarge := true
  }

def mkSEvalContext : MetaM Context := do
  let s ← getSEvalTheorems
  let c ← Meta.getSimpCongrTheorems
  mkContext
    (simpTheorems := #[s])
    (congrTheorems := c)
    (config := { ground := true })

/--
Invoke ground/symbolic evaluator from `simp`.
It uses the `seval` theorems and simprocs.
-/
def seval (e : Expr) : SimpM Result := do
  let m ← mkSEvalMethods
  let ctx ← mkSEvalContext
  let cacheSaved := (← get).cache
  let usedTheoremsSaved := (← get).usedTheorems
  try
    withReader (fun _ => m.toMethodsRef) do
    withTheReader Simp.Context (fun _ => ctx) do
    modify fun s => { s with cache := {}, usedTheorems := {} }
    simp e
  finally
    modify fun s => { s with cache := cacheSaved, usedTheorems := usedTheoremsSaved }

/--
Try to unfold ground term in the ground/symbolic evaluator.
-/
def simpGround : Simproc := fun e => do
  -- Ground term unfolding is disabled.
  unless (← getConfig).ground do return .continue
  -- `e` is not a ground term.
  unless !e.hasExprMVar && !e.hasFVar do return .continue
  -- Check whether `e` is a constant application
  let f := e.getAppFn
  let .const declName _ := f | return .continue
  -- If declaration has been marked to not be unfolded, return none.
  let ctx ← getContext
  if ctx.simpTheorems.isErased (.decl declName) then return .continue
  -- Matcher applications should have been reduced before we get here.
  if (← isMatcher declName) then return .continue
  let r ← withTraceNode `Meta.Tactic.simp.ground (fun
      | .ok r => return m!"seval: {e} => {r.expr}"
      | .error err => return m!"seval: {e} => {err.toMessageData}") do
    seval e
  return .done r

def preDefault (s : SimprocsArray) : Simproc :=
  rewritePre >>
  simpMatch >>
  userPreSimprocs s >>
  simpUsingDecide

def postDefault (s : SimprocsArray) : Simproc :=
  rewritePost >>
  userPostSimprocs s >>
  simpGround >>
  simpArith >>
  simpUsingDecide

/--
  Return true if `e` is of the form `(x : α) → ... → s = t → ... → False`

  Recall that this kind of proposition is generated by Lean when creating equations for
  functions and match-expressions with overlapping cases.
  Example: the following `match`-expression has overlapping cases.
  ```
  def f (x y : Nat) :=
    match x, y with
    | Nat.succ n, Nat.succ m => ...
    | _, _ => 0
  ```
  The second equation is of the form
  ```
  (x y : Nat) → ((n m : Nat) → x = Nat.succ n → y = Nat.succ m → False) → f x y = 0
  ```
  The hypothesis `(n m : Nat) → x = Nat.succ n → y = Nat.succ m → False` is essentially
  saying the first case is not applicable.
-/
partial def isEqnThmHypothesis (e : Expr) : Bool :=
  e.isForall && go e
where
  go (e : Expr) : Bool :=
    match e with
    | .forallE _ d b _ => (d.isEq || d.isHEq || b.hasLooseBVar 0) && go b
    | _ => e.isFalse

private def dischargeUsingAssumption? (e : Expr) : SimpM (Option Expr) := do
  let lctxInitIndices := (← readThe Simp.Context).lctxInitIndices
  let contextual := (← getConfig).contextual
  (← getLCtx).findDeclRevM? fun localDecl => do
    if localDecl.isImplementationDetail then
      return none
    -- The following test is needed to ensure `dischargeUsingAssumption?` is a
    -- well-behaved discharger. See comment at `Methods.wellBehavedDischarge`
    else if !contextual && localDecl.index >= lctxInitIndices then
      return none
    else if (← withSimpMetaConfig <| isDefEq e localDecl.type) then
      return some localDecl.toExpr
    else
      return none

/--
  Tries to solve `e` using `unifyEq?`.
  It assumes that `isEqnThmHypothesis e` is `true`.
-/
partial def dischargeEqnThmHypothesis? (e : Expr) : MetaM (Option Expr) := do
  assert! isEqnThmHypothesis e
  let mvar ← mkFreshExprSyntheticOpaqueMVar e
  withCanUnfoldPred canUnfoldAtMatcher do
    if let .none ← go? mvar.mvarId! then
      instantiateMVars mvar
    else
      return none
where
  go? (mvarId : MVarId) : MetaM (Option MVarId) :=
    try
      let (fvarId, mvarId) ← mvarId.intro1
      mvarId.withContext do
        let localDecl ← fvarId.getDecl
        if localDecl.type.isEq || localDecl.type.isHEq then
          if let some { mvarId, .. } ← unifyEq? mvarId fvarId {} then
            go? mvarId
          else
            return none
        else
          go? mvarId
    catch _  =>
      return some mvarId

/--
Discharges assumptions of the form `∀ …, a = b` using `rfl`. This is particularly useful for higher
order assumptions of the form `∀ …, e = ?g x y` to instaniate  a parameter `g` even if that does not
appear on the lhs of the rule.
-/
def dischargeRfl (e : Expr) : SimpM (Option Expr) := do
  forallTelescope e fun xs e => do
    let some (t, a, b) := e.eq? | return .none
    unless a.getAppFn.isMVar || b.getAppFn.isMVar do return .none
    if (← withSimpMetaConfig <| isDefEq a b) then
      trace[Meta.Tactic.simp.discharge] "Discharging with rfl: {e}"
      let u ← getLevel t
      let proof := mkApp2 (.const ``rfl [u]) t a
      let proof ← mkLambdaFVars xs proof
      return .some proof
    return .none


def dischargeDefault? (e : Expr) : SimpM (Option Expr) := do
  let e := e.cleanupAnnotations
  if isEqnThmHypothesis e then
    if let some r ← dischargeUsingAssumption? e then return some r
    if let some r ← dischargeEqnThmHypothesis? e then return some r
  let r ← simp e
  if let some p ← dischargeRfl r.expr then
    return some (← mkEqMPR (← r.getProof) p)
  else if r.expr.isTrue then
    return some (← mkOfEqTrue (← r.getProof))
  else
    return none

abbrev Discharge := Expr → SimpM (Option Expr)

def mkMethods (s : SimprocsArray) (discharge? : Discharge) (wellBehavedDischarge : Bool) : Methods := {
  pre        := preDefault s
  post       := postDefault s
  dpre       := dpreDefault s
  dpost      := dpostDefault s
  discharge?
  wellBehavedDischarge
}

def mkDefaultMethodsCore (simprocs : SimprocsArray) : Methods :=
  mkMethods simprocs dischargeDefault? (wellBehavedDischarge := true)

def mkDefaultMethods : CoreM Methods := do
  if simprocs.get (← getOptions) then
    return mkDefaultMethodsCore #[(← getSimprocs)]
  else
    return mkDefaultMethodsCore {}

end Lean.Meta.Simp
