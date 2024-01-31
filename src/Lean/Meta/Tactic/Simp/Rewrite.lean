/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.ACLt
import Lean.Meta.Match.MatchEqsExt
import Lean.Meta.AppBuilder
import Lean.Meta.SynthInstance
import Lean.Meta.Tactic.UnifyEq
import Lean.Meta.Tactic.Simp.Types
import Lean.Meta.Tactic.LinearArith.Simp
import Lean.Meta.Tactic.Simp.Simproc

namespace Lean.Meta.Simp

def synthesizeArgs (thmId : Origin) (xs : Array Expr) (bis : Array BinderInfo) : SimpM Bool := do
  for x in xs, bi in bis do
    let type ← inferType x
    -- Note that the binderInfo may be misleading here:
    -- `simp [foo _]` uses `abstractMVars` to turn the elaborated term with
    -- mvars into the lambda expression `fun α x inst => foo x`, and all
    -- its bound variables have default binderInfo!
    if bi.isInstImplicit then
      unless (← synthesizeInstance x type) do
        return false
    else if (← instantiateMVars x).isMVar then
      -- A hypothesis can be both a type class instance as well as a proposition,
      -- in that case we try both TC synthesis and the discharger
      -- (because we don't know whether the argument was originally explicit or instance-implicit).
      if (← isClass? type).isSome then
        if (← synthesizeInstance x type) then
          continue
      if (← isProp type) then
        -- We save the state, so that `UsedTheorems` does not accumulate
        -- `simp` lemmas used during unsuccessful discharging.
        let usedTheorems := (← get).usedTheorems
        match (← discharge? type) with
        | some proof =>
          unless (← isDefEq x proof) do
            trace[Meta.Tactic.simp.discharge] "{← ppOrigin thmId}, failed to assign proof{indentExpr type}"
            modify fun s => { s with usedTheorems }
            return false
        | none =>
          trace[Meta.Tactic.simp.discharge] "{← ppOrigin thmId}, failed to discharge hypotheses{indentExpr type}"
          modify fun s => { s with usedTheorems }
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

private def tryTheoremCore (lhs : Expr) (xs : Array Expr) (bis : Array BinderInfo) (val : Expr) (type : Expr) (e : Expr) (thm : SimpTheorem) (numExtraArgs : Nat) : SimpM (Option Result) := do
  let rec go (e : Expr) : SimpM (Option Result) := do
    if (← isDefEq lhs e) then
      unless (← synthesizeArgs thm.origin xs bis) do
        return none
      let proof? ← if thm.rfl then
        pure none
      else
        let proof ← instantiateMVars (mkAppN val xs)
        if (← hasAssignableMVar proof) then
          trace[Meta.Tactic.simp.rewrite] "{← ppSimpTheorem thm}, has unassigned metavariables after unification"
          return none
        pure <| some proof
      let rhs := (← instantiateMVars type).appArg!
      if e == rhs then
        return none
      if thm.perm then
        /-
        We use `.reduceSimpleOnly` because this is how we indexed the discrimination tree.
        See issue #1815
        -/
        if !(← Expr.acLt rhs e .reduceSimpleOnly) then
          trace[Meta.Tactic.simp.rewrite] "{← ppSimpTheorem thm}, perm rejected {e} ==> {rhs}"
          return none
      trace[Meta.Tactic.simp.rewrite] "{← ppSimpTheorem thm}, {e} ==> {rhs}"
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
  let candidates ← s.getMatchWithExtra e (getDtConfig (← getConfig))
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
where
  inErasedSet (thm : SimpTheorem) : Bool :=
    erased.contains thm.origin

-- TODO: workaround for `Expr.constructorApp?` limitations. We should handle `OfNat.ofNat` there
private def reduceOfNatNat (e : Expr) : MetaM Expr := do
  unless e.isAppOfArity ``OfNat.ofNat 3 do
    return e
  unless (← whnfD (e.getArg! 0)).isConstOf ``Nat do
    return e
  return e.getArg! 1

def simpCtorEq : Simproc := fun e => withReducibleAndInstances do
  match e.eq? with
  | none => return .continue
  | some (_, lhs, rhs) =>
    let lhs ← reduceOfNatNat (← whnf lhs)
    let rhs ← reduceOfNatNat (← whnf rhs)
    let env ← getEnv
    match lhs.constructorApp? env, rhs.constructorApp? env with
    | some (c₁, _), some (c₂, _) =>
      if c₁.name != c₂.name then
        withLocalDeclD `h e fun h =>
          return .done { expr := mkConst ``False, proof? := (← withDefault <| mkEqFalse' (← mkLambdaFVars #[h] (← mkNoConfusion (mkConst ``False) h))) }
      else
        return .continue
    | _, _ => return .continue

@[inline] def simpUsingDecide : Simproc := fun e => do
  unless (← getConfig).decide do
    return .continue
  if e.hasFVar || e.hasMVar || e.consumeMData.isConstOf ``True || e.consumeMData.isConstOf ``False then
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
  if Linear.isLinearCnstr e then
    let some (e', h) ← Linear.Nat.simpCnstr? e
      | return .continue
    return .visit { expr := e', proof? := h }
  else if Linear.isLinearTerm e then
    if Linear.parentIsTarget (← getContext).parent? then
      -- We mark `cache := false` to ensure we do not miss simplifications.
      return .continue (some { expr := e, cache := false })
    let some (e', h) ← Linear.Nat.simpExpr? e
      | return .continue
    return .visit { expr := e', proof? := h }
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
  for i in [info.numDiscrs : args.size] do
    let arg := args[i]!
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
  if let some e ← reduceRecMatcher? e then
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

/--
Discharge procedure for the ground/symbolic evaluator.
-/
def dischargeGround (e : Expr) : SimpM (Option Expr) := do
  trace[Meta.Tactic.simp.discharge] ">> discharge?: {e}"
  let r ← simp e
  if r.expr.consumeMData.isConstOf ``True then
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
  sevalGround >>
  simpCtorEq

def mkSEvalMethods : CoreM Methods := do
  let s ← getSEvalSimprocs
  return {
    pre        := preSEval #[s]
    post       := postSEval #[s]
    discharge? := dischargeGround
  }

def mkSEvalContext : CoreM Context := do
  let s ← getSEvalTheorems
  let c ← Meta.getSimpCongrTheorems
  return { simpTheorems := #[s], congrTheorems := c, config := { ground := true } }

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
  trace[Meta.Tactic.Simp.ground] "seval: {e}"
  let r ← seval e
  trace[Meta.Tactic.Simp.ground] "seval result: {e} => {r.expr}"
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
  simpCtorEq >>
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
    | _ => e.consumeMData.isConstOf ``False

def dischargeUsingAssumption? (e : Expr) : SimpM (Option Expr) := do
  (← getLCtx).findDeclRevM? fun localDecl => do
    if localDecl.isImplementationDetail then
      return none
    else if (← isDefEq e localDecl.type) then
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
  withReader (fun ctx => { ctx with canUnfold? := canUnfoldAtMatcher }) do
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

def dischargeDefault? (e : Expr) : SimpM (Option Expr) := do
  if isEqnThmHypothesis e then
    if let some r ← dischargeUsingAssumption? e then
      return some r
    if let some r ← dischargeEqnThmHypothesis? e then
      return some r
  let ctx ← getContext
  trace[Meta.Tactic.simp.discharge] ">> discharge?: {e}"
  if ctx.dischargeDepth >= ctx.maxDischargeDepth then
    trace[Meta.Tactic.simp.discharge] "maximum discharge depth has been reached"
    return none
  else
    withTheReader Context (fun ctx => { ctx with dischargeDepth := ctx.dischargeDepth + 1 }) do
      let r ← simp e
      if r.expr.consumeMData.isConstOf ``True then
        try
          return some (← mkOfEqTrue (← r.getProof))
        catch _ =>
          return none
      else
        return none

abbrev Discharge := Expr → SimpM (Option Expr)

def mkMethods (s : SimprocsArray) (discharge? : Discharge) : Methods := {
  pre        := preDefault s
  post       := postDefault s
  discharge? := discharge?
}

def mkDefaultMethodsCore (simprocs : SimprocsArray) : Methods :=
  mkMethods simprocs dischargeDefault?

def mkDefaultMethods : CoreM Methods := do
  if simprocs.get (← getOptions) then
    return mkDefaultMethodsCore #[(← getSimprocs)]
  else
    return mkDefaultMethodsCore {}

end Lean.Meta.Simp
