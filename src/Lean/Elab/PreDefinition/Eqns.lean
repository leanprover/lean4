/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Joachim Breitner
-/
module
prelude
import Lean.Elab.PreDefinition.EqnsUtils
import Lean.Meta.HaveTelescope
import Lean.Meta.LetToHave
import Lean.Meta.Match.NamedPatterns
import Lean.Meta.Match.Rewrite
import Lean.Meta.Tactic.Simp.Main
import Lean.Meta.Tactic.Split
import Lean.Meta.Tactic.SplitIf
import Lean.Meta.Tactic.CasesOnStuckLHS

/-!
This module implements the generation of equational theorems, given unfolding theorems.
The unfolding theorems are generated differently for different kinds of recursive definition,
but the code here no longer cares about that.

-/

namespace Lean.Elab.Eqns
open Meta

/--
Returns the type of the unfold theorem, as the starting point for calculating the equational
types. See `unfoldLHS` to do the unfolding.
-/
def unfoldThmType (declName : Name) : MetaM Expr := do
  if let some unfoldThm ← getUnfoldEqnFor? declName (nonRec := false) then
    let info ← getConstInfo unfoldThm
    pure info.type
  else
    let info ← getConstInfoDefn declName
    let us := info.levelParams.map mkLevelParam
    lambdaTelescope (cleanupAnnotations := true) info.value fun xs body => do
      let type ← mkEq (mkAppN (Lean.mkConst declName us) xs) body
      mkForallFVars xs type

/--
Unfolds the application of `declName` on the left-hand side of an equality goal, using its
unfolding theorem when available and delta reduction otherwise.
-/
def unfoldLHS (declName : Name) (mvarId : MVarId) : MetaM MVarId := mvarId.withContext do
  if let some unfoldThm ← getUnfoldEqnFor? declName (nonRec := false) then
    -- Recursive definition: Use unfolding lemma
    let mut mvarId := mvarId
    let target ← mvarId.getType'
    let some (_, lhs, rhs) := target.eq? | throwError "unfoldLHS: Unexpected target {target}"
    unless lhs.isAppOf declName do throwError "unfoldLHS: Unexpected LHS {lhs}"
    let h := mkAppN (.const unfoldThm lhs.getAppFn.constLevels!) lhs.getAppArgs
    let some (_, _, lhsNew) := (← inferType h).eq? | unreachable!
    let targetNew ← mkEq lhsNew rhs
    let mvarNew ← mkFreshExprSyntheticOpaqueMVar targetNew
    mvarId.assign (← mkEqTrans h mvarNew)
    return mvarNew.mvarId!
  else
    -- Else use delta reduction
    deltaLHS mvarId

/--
Proves a generated equation type for `declName`. After introducing its parameters and hypotheses,
tries reflexivity, then unfolds the definition and reduces or splits the remaining cases.
-/
partial def mkEqnProof (declName : Name) (type : Expr) : MetaM Expr := do
  withTraceNode `Elab.definition.eqns (fun _ => return m!"proving:{indentExpr type}") do
  withNewMCtxDepth do
    let main ← mkFreshExprSyntheticOpaqueMVar type
    let (_, mvarId) ← main.mvarId!.intros

    -- Try rfl before deltaLHS to avoid `id` checkpoints in the proof, which would make
    -- the lemma ineligible for dsimp
    if (← tryURefl mvarId #[declName]) then
      trace[Elab.definition.eqns] "proved directly by rfl"
      return ← instantiateMVars main

    go (← unfoldLHS declName mvarId)
    instantiateMVars main
  where
  /--
  The core loop of proving an equation. Assumes that the function call on the left-hand side has
  already been unfolded, using whatever method applies to the current function definition strategy.

  Currently used for non-recursive functions and partial fixpoints; maybe later well-founded
  recursion and structural recursion can and should use this too.
  -/
  go (mvarId : MVarId) : MetaM Unit := do
    withTraceNode `Elab.definition.eqns (fun _ => return m!"step:\n{MessageData.ofGoal mvarId}") do
    if (← tryURefl mvarId) then
      return ()
    else if (← tryContradiction mvarId) then
      return ()
    else if let some mvarId ← simpMatch? mvarId then
      go mvarId
    else if let some mvarId ← simpIf? mvarId (useNewSemantics := true) then
      go mvarId
    else if let some mvarId ← whnfReducibleLHS? mvarId then
      go mvarId
    else
      let ctx ← Simp.mkContext (config := { dsimp := false })
      match (← simpTargetStar mvarId ctx (simprocs := {})).1 with
      | TacticResultCNM.closed => return ()
      | TacticResultCNM.modified mvarId => go mvarId
      | TacticResultCNM.noChange =>
        if let some mvarIds ← casesOnStuckLHS? mvarId then
          mvarIds.forM go
        else if let some mvarIds ← splitTarget? mvarId (useNewSemantics := true) then
          mvarIds.forM go
        else
          throwError "failed to generate equational theorem for `{.ofConstName declName}`\n{MessageData.ofGoal mvarId}"

/--
Checks whether the left-hand side of a quantified equality depends on `fvarId`.
For a non-equality conclusion, checks the entire conclusion.
-/
def lhsDependsOn (type : Expr) (fvarId : FVarId) : MetaM Bool :=
  forallTelescope type fun _ type => do
    if let some (_, lhs, _) ← matchEq? type then
      dependsOn lhs fvarId
    else
      dependsOn type fvarId

/-- Eliminates named-pattern annotations and redundant equality hypotheses from an equation type. -/
def simpEqnType (eqnType : Expr) : MetaM Expr := do
  forallTelescopeReducing (← instantiateMVars eqnType) fun ys type => do
    let proofVars := collect type
    trace[Elab.definition] "simpEqnType type: {type}"
    let mut type ← Match.unfoldNamedPattern type
    let mut eliminated : FVarIdSet := {}
    for y in ys.reverse do
      trace[Elab.definition] ">> simpEqnType: {← inferType y}, {type}"
      if proofVars.contains y.fvarId! then
        let some (_, Expr.fvar fvarId, rhs) ← matchEq? (← inferType y) | throwError "unexpected hypothesis in alternative{indentExpr eqnType}"
        eliminated := eliminated.insert fvarId
        type := type.replaceFVarId fvarId rhs
      else if eliminated.contains y.fvarId! then
        if (← dependsOn type y.fvarId!) then
          type ← mkForallFVars #[y] type
      else
        if let some (_, lhs, rhs) ← matchEq? (← inferType y) then
          if (← isDefEq lhs rhs) then
            if !(← dependsOn type y.fvarId!) then
              continue
            else if !(← lhsDependsOn type y.fvarId!) then
              -- Since the `lhs` of the `type` does not depend on `y`, we replace it with `Eq.refl` in the `rhs`
              type := type.replaceFVar y (← mkEqRefl lhs)
              continue
        type ← mkForallFVars #[y] type
    return type
where
  -- Collect eq proof vars used in `namedPatterns`
  collect (e : Expr) : FVarIdSet :=
    let go (e : Expr) (ω) : ST ω FVarIdSet := do
      let ref ← ST.mkRef {}
      e.forEachWhere Match.isNamedPattern fun e => do
        let some e := Match.isNamedPattern? e | unreachable!
        let arg := e.appArg!.consumeMData
        if arg.isFVar then
          ST.Prim.Ref.modify ref (·.insert arg.fvarId!)
      ST.Prim.Ref.get ref
    runST (go e)


/--
Closes a terminal goal over its free variables and relevant propositional hypotheses, simplifies
the resulting equation type, and appends it to the state. RHS bindings remain inside the target.
-/
partial def saveEqn (mvarId : MVarId) : StateRefT (Array Expr) MetaM Unit := mvarId.withContext do
  let target ← mvarId.getType'
  let fvarState := collectFVars {} target
  let fvarState ← (← getLCtx).foldrM (init := fvarState) fun decl fvarState => do
    if fvarState.fvarSet.contains decl.fvarId then
      return collectFVars fvarState (← instantiateMVars decl.type)
    else
      return fvarState
  let mut fvarIdSet := fvarState.fvarSet
  let mut fvarIds ← sortFVarIds <| fvarState.fvarSet.toArray
  -- Include (relevant) propositions that are not already in `fvarIdSet`
  let mut modified := false
  repeat
    modified := false
    for decl in (← getLCtx) do
      unless fvarIdSet.contains decl.fvarId do
        if (← isProp decl.type) then
          let type ← instantiateMVars decl.type
          unless (← isIrrelevant fvarIdSet type) do
            modified := true
            (fvarIdSet, fvarIds) ← pushDecl fvarIdSet fvarIds decl
  until !modified
  let type ← mkForallFVars (fvarIds.map mkFVar) target
  let type ← simpEqnType type
  modify (·.push type)
where
  /--
    We say the type/proposition is "irrelevant" if
    1- It does not contain any variable in `fvarIdSet` OR
    2- It is of the form `x = t` or `t = x` where `x` is a free variable
       that is not in `fvarIdSet`. This kind of equality can be eliminated by substitution.  -/
  isIrrelevant (fvarIdSet : FVarIdSet) (type : Expr) : MetaM Bool := do
    if Option.isNone <| type.find? fun e => e.isFVar && fvarIdSet.contains e.fvarId! then
      return true
    else if let some (_, lhs, rhs) := type.eq? then
      return (lhs.isFVar && !fvarIdSet.contains lhs.fvarId!)
             || (rhs.isFVar && !fvarIdSet.contains rhs.fvarId!)
    else
      return false

  /-- Adds a declaration after recursively collecting the dependencies of its type. -/
  pushDecl (fvarIdSet : FVarIdSet) (fvarIds : Array FVarId) (localDecl : LocalDecl) : MetaM (FVarIdSet × Array FVarId) := do
    let (fvarIdSet, fvarIds) ← collectDeps fvarIdSet fvarIds (← instantiateMVars localDecl.type)
    return (fvarIdSet.insert localDecl.fvarId, fvarIds.push localDecl.fvarId)

  /-- Extends the selected declarations with the transitive type dependencies of `type`. -/
  collectDeps (fvarIdSet : FVarIdSet) (fvarIds : Array FVarId) (type : Expr) : MetaM (FVarIdSet × Array FVarId) := do
    let s := collectFVars {} type
    let usedFVarIds ← sortFVarIds <| s.fvarSet.toArray
    let mut fvarIdSet := fvarIdSet
    let mut fvarIds := fvarIds
    for fvarId in usedFVarIds do
      unless fvarIdSet.contains fvarId do
        (fvarIdSet, fvarIds) ← pushDecl fvarIdSet fvarIds (← fvarId.getDecl)
    return (fvarIdSet, fvarIds)

/--
A matcher splitter invocation whose arguments are well-scoped in the goal's local context.
Dependencies on bindings inside the RHS are enclosed in `let`/`have` expressions in the arguments.
-/
structure MatchToSplit where
  declName : Name
  levels : Array Level
  params : Array Expr
  discrs : Array Expr
  deriving BEq, Hashable

/--
Follows a chain of local `let`/`have` aliases until reaching an ordinary variable or a non-variable
value. Only aliases at the head are followed; subexpressions of the value remain shared.
-/
partial def resolveLetVar (e : Expr) : MetaM Expr := do
  match e.consumeMData with
  | .fvar fvarId =>
    if let some value := (← fvarId.getDecl).value? (allowNondep := true) then
      resolveLetVar value
    else
      return e
  | _ => return e

/--
Finds the first eligible matcher in `rhs` whose splitter invocation is not in `exceptions`.
At least one discriminant must resolve to a variable in the goal's local context. Enclosing RHS
bindings are closed over the splitter arguments; captures of enclosing lambda or alternative
parameters make a matcher ineligible.

Binding values are searched before their bodies. For recursive definitions, unless deep splitting
is enabled, a candidate must have an alternative with a recursive call depending on its binders.
-/
partial def findMatchToSplit? (rhs : Expr) (declNames : Array Name)
    (exceptions : Std.HashSet MatchToSplit) : MetaM (Option MatchToSplit) := do
  let outer ← getLCtx
  let deep := backward.eqns.deepRecursiveSplit.get (← getOptions)
  visit outer deep #[] rhs
where
  visit (outer : LocalContext) (deep : Bool) (lets : Array Expr) (e : Expr) :
      MetaM (Option MatchToSplit) := do
    checkSystem "findMatchToSplit"
    if let some app ← matchMatcherApp? e then
      let eligible := declNames.isEmpty || deep || app.alts.any fun alt =>
        (alt.find? fun e => declNames.any e.isAppOf && e.hasLooseBVars).isSome
      if eligible then
        let hasVar ← app.discrs.anyM fun discr => do
          let discr ← resolveLetVar discr
          return discr.isFVar && outer.contains discr.fvarId!
        if hasVar then
          let closed ← mkLetFVars lets e (generalizeNondepLet := false)
          -- Captures of enclosing lambdas and match alternatives prevent a split.
          if !closed.hasAnyFVar (fun x => !outer.contains x) then
            let params ← app.params.mapM fun e => mkLetFVars lets e (generalizeNondepLet := false)
            let discrs ← app.discrs.mapM fun e => do
              let resolved ← resolveLetVar e
              mkLetFVars lets resolved (generalizeNondepLet := false)
            unless (params ++ discrs).any (fun e => e.hasAnyFVar fun x => !outer.contains x) do
              let candidate := { declName := app.matcherName, levels := app.matcherLevels, params, discrs }
              unless exceptions.contains candidate do return some candidate
    if let .const name _ := e.getAppFn then
      if name == ``WellFounded.fix || isBRecOnRecursor (← getEnv) name then
        return none
    match e with
    | .letE .. =>
      letTelescope e fun xs body => do
        let mut lets := lets
        for x in xs do
          if let some candidate ← visit outer deep lets ((← x.fvarId!.getDecl).value (allowNondep := true)) then
            return some candidate
          lets := lets.push x
        visit outer deep lets body
    | .lam n t b bi | .forallE n t b bi =>
      withLocalDecl n bi t fun x => visit outer deep lets (b.instantiate1 x)
    | .app .. =>
      if !e.getAppFn.isConst then
        if let some candidate ← visit outer deep lets e.getAppFn then return some candidate
      for arg in e.getAppArgs do
        if let some candidate ← visit outer deep lets arg then return some candidate
      return none
    | .mdata _ b | .proj _ _ b => visit outer deep lets b
    | _ => return none

/--
Result of simplifying a telescope suffix. All fields use loose bound variables for the preceding
bindings. `proof?`, when present, proves equality from the original suffix to `expr`; otherwise
the change is definitional. `type` is the type of the suffix in that prefix context.
-/
structure EqnTelescopeResult where
  expr : Expr
  type : Expr
  proof? : Option Expr := none

/--
Simplifies the suffix `e` beginning at binding `i` of the telescope described by `info`.
The preceding bindings are represented by free variables in `xs` and the cached expressions in
`info`, but by loose bound variables in `e` and the result. Abstraction is batched so that closing
each binder does not repeatedly traverse the entire remaining body and proof.

Unused values are skipped. Fixed values admit only `dsimp`; other values admit propositional
rewrites. Each updated value is entered as a dependent local definition so that matcher reduction
can use its value while simplifying the remainder. The simplifier cache is isolated for that
scope. A changed body is rebuilt with `let`; `simpEqn` then uses `letToHave` to recover `have`
bindings where their bodies remain well typed with the variable abstract.

A value rewrite is lifted with `congrArg (fun x => originalBody)`. The body proof is closed with
`let x := updatedValue`, since it may rely on that value; the two proofs compose by transitivity.
For a nonfixed binding the result type cannot depend on `x`, so its bound-variable slot is removed.
For a fixed binding the result type is closed with the binding itself.
-/
partial def simpEqnTelescope (info : HaveTelescopeInfo) (fixed used : Array Bool)
    (e : Expr) (i : Nat) (xs : Array Expr) : Simp.SimpM EqnTelescopeResult := do
  if h : i < info.haveInfo.size then
    let hi := info.haveInfo[i]
    /-
    **Note**: `hi.decl` has no loose de-Bruijn indices, but `t`, `v`, and `b` might have.
    We extract them from `e` to avoid unnecessary `abstract` steps.
    -/
    let .letE n t v b nondep := e | unreachable!
    let x := hi.decl.toExpr
    let val := hi.decl.value (allowNondep := true)
    let rv ← if !used[i]! then pure { expr := val }
      else if fixed[i]! then pure { expr := (← Simp.dsimp val) }
      else Simp.simp val
    let v' := if rv.expr == val then v else rv.expr.abstract xs
    let hv? := rv.proof?.map (·.abstract xs)
    /-
    Given `have a := 0; ... match a with | 0 => ... | _ => ...`,
    we want to make sure `a` is transparent when reducing the `match`.
    -/
    let decl := (hi.decl.setValue rv.expr).setNondep false
    let rb ← withExistingLocalDecls [decl] <| Simp.withNewLemmas #[x] do
      simpEqnTelescope info fixed used b (i + 1) (xs.push x)
    let type := if fixed[i]! then
      /- A fixed binding may occur in the result type, so close the type with the binding. -/
      mkLet n t v' rb.type false
    else
      /- The type does not depend on this binding; remove its unused bound-variable slot. -/
      rb.type.lowerLooseBVars 1 1
    /- A changed body may need the value of `x` to typecheck. Use `let` until `letToHave`
    checks whether the body can still be abstracted over `x`. -/
    let expr := mkLet n t v' rb.expr (nondep && rb.expr == b)
    let hb? := rb.proof?.map fun h => mkLet n t v' h false
    let hv? := hv?.map fun h => mkApp6 (mkConst ``congrArg [hi.level, info.level])
      t type v v' (mkLambda n .default t b) h
    let proof? := match hv?, hb? with
      | none, hb? => hb?
      | hv?, none => hv?
      | some hv, some hb => some <| mkEqTransCore info.level type e
          (mkLet n t v' b nondep) expr hv hb
    return { expr, type, proof? }
  else
    /- Simplify the body. -/
    let rb ← Simp.simp info.body
    return {
      expr := if rb.expr == info.body then e else rb.expr.abstract xs
      type := info.bodyType.abstract xs
      proof? := rb.proof?.map (·.abstract xs)
    }

/--
Opens a leading telescope of mixed `let`/`have` bindings once and records its declarations,
instantiated body, and dependencies between bindings.

`computeFixedUsed false` then computes two dependency closures: `used` starts from the body;
`fixed` starts from its result type and every dependent `let`. A dependent let's body may rely on
its value to typecheck even when the result type does not mention it, so that value and its
dependencies must be restricted to definitional simplification.
-/
def getEqnTelescopeInfo (e : Expr) : MetaM HaveTelescopeInfo := do
  letTelescope e fun xs body => do
    let mut indices : Std.HashMap FVarId Nat := {}
    for i in *...xs.size do
      indices := indices.insert xs[i]!.fvarId! i
    let getDeps (e : Expr) : Std.HashSet Nat :=
      (collectFVars {} e).fvarIds.foldl (init := {}) fun deps id =>
        match indices[id]? with
        | none => deps
        | some i => deps.insert i
    let bodyType ← inferType body
    let mut info : HaveTelescopeInfo := {
      body, bodyType
      level := ← getLevel bodyType
      bodyDeps := getDeps body
      bodyTypeDeps := getDeps bodyType
    }
    for i in *...xs.size do
      let decl ← xs[i]!.fvarId!.getDecl
      let hi : HaveInfo := {
        decl
        level := ← getLevel decl.type
        typeBackDeps := getDeps decl.type
        valueBackDeps := getDeps (decl.value (allowNondep := true))
      }
      info := { info with haveInfo := info.haveInfo.push hi }
      unless decl.isNondep do
        info := { info with bodyTypeDeps := info.bodyTypeDeps.insert i }
    return info

/--
The `simp` callback for equation normalization. It handles complete binding telescopes before the
default traversal, using `simpEqnTelescope` to preserve their nesting and sharing. Unused bindings
are removed afterward, and `letToHave` determines which bindings can be nondependent.
A changed telescope is revisited: removing dependent uses or restoring a `have` can make a
previously fixed value eligible for propositional rewriting. A stable telescope returns `.done`.

For a matcher, first try definitional reduction, then its congruence equations using local
hypotheses to discharge branch conditions. Other expressions use the default traversal.
Since matcher rewriting can use hypotheses introduced under binders, callers with
`contextual := false` must set `wellBehavedDischarge := false` to isolate cached results by scope.
-/
partial def simpEqn : Simp.Simproc := fun e => do
  if e.isLet then
    let info ← getEqnTelescopeInfo e
    let (fixed, used) ← info.computeFixedUsed false
    let r ← simpEqnTelescope info fixed used e 0 #[]
    let r := { expr := ← zetaUnused r.expr, proof? := r.proof? : Simp.Result }
    if r.expr == e then return .done r
    return .visit { r with expr := (← letToHave r.expr) }
  if let some app ← matchMatcherApp? e then
    if let some e' ← reduceRecMatcher? e then
      return .visit { expr := e' }
    for i in *...app.numAlts do
      let r ← rwMatcher i e
      if r.expr != e then return .visit r
  return .continue

/--
The definitional counterpart of `simpEqn`, used for fixed binding values and dependent arguments
that `simp` cannot rewrite propositionally. It opens a whole binding telescope, skips unused
values, and definitionally simplifies the other values and body with preceding values available
as local definitions. Changed bodies are rebuilt with `let`, and `letToHave` recovers `have`
bindings where possible. Unused bindings are removed.

Matchers are reduced only definitionally; no congruence-equation proofs are used. Changed results
are revisited, and the returned expression is definitionally equal to the input.
-/
partial def dsimpEqn : Simp.DSimproc := fun e => do
  if e.isLet then
    let info ← getEqnTelescopeInfo e
    let (_, used) ← info.computeFixedUsed false
    let r ← Simp.withFreshCache <| visit info used e 0 #[]
    let r ← zetaUnused r
    if r == e then return .done r
    return .visit (← letToHave r)
  if ← isMatcherApp e then
    if let some e' ← reduceRecMatcher? e then return .visit e'
  return .continue
where
  visit (info : HaveTelescopeInfo) (used : Array Bool) (e : Expr) (i : Nat)
      (xs : Array Expr) : Simp.SimpM Expr := do
    if h : i < info.haveInfo.size then
      let decl := info.haveInfo[i].decl
      /-
      **Note**: `decl` has no loose de-Bruijn indices, but `t`, `v`, and `b` might have.
      We extract them from `e` to avoid unnecessary `abstract` steps.
      -/
      let .letE n t v b nondep := e | unreachable!
      /- Recall that the original `decl` may be a `have`, and without `allowNondep := true`, `value` will fail. -/
      let value := decl.value (allowNondep := true)
      let value' ← if used[i]! then Simp.dsimp value else pure value
      let v' := if value' == value then v else value'.abstract xs
      /-
      Given `have a := 0; ... match a with | 0 => ... | _ => ...`,
      we want to make sure `a` is transparent when reducing the `match`.
      -/
      let decl := (decl.setValue value').setNondep false
      let b' ← withExistingLocalDecls [decl] <| visit info used b (i+1) (xs.push decl.toExpr)
      /- As in `simpEqnTelescope`, a changed body must be checked before retaining `have`. -/
      return mkLet n t v' b' (nondep && b' == b)
    else
      return (← Simp.dsimp info.body).abstract xs

/--
Normalizes the RHS of an equality goal using `simpEqn` and `dsimpEqn`, preserving shared bindings.
The neutral configuration disables general reductions, including zeta expansion, while `simp`
provides traversal and congruence. Propositional RHS rewrites are lifted to the whole target;
definitional rewrites directly replace the target.
Returns the original goal when unchanged, which lets `splitMatch?` detect normalization progress.
-/
def normalizeEqn (mvarId : MVarId) : MetaM MVarId := mvarId.withContext do
  let target ← mvarId.getType'
  let some (_, lhs, rhs) := target.eq? | return mvarId
  let ctx ← Simp.mkContext (config := { Simp.neutralConfig with dsimp := true, etaStruct := .none })
  let methods : Simp.Methods := {
    pre := simpEqn
    dpre := dsimpEqn
    discharge? := ← SplitIf.mkDischarge?
    -- Matcher rewrites can use hypotheses introduced while descending under binders.
    wellBehavedDischarge := false
  }
  let (r, _) ← Simp.main rhs ctx (methods := methods)
  if r.expr == rhs then return mvarId
  let target' ← mkEq lhs r.expr
  if let some proof := r.proof? then
    let eq := target.appFn!
    return ← mvarId.replaceTargetEq target' (← mkCongrArg eq proof)
  else
    mvarId.replaceTargetDefEq target'

/--
Tries eligible RHS matchers until a splitter produces branches whose RHSs all change under
normalization. Each attempt saves the metavariable state; failure restores it and excludes that
splitter invocation from further attempts. Returned branches are already normalized.
-/
partial def splitMatch? (mvarId : MVarId) (declNames : Array Name) :
    MetaM (Option (List MVarId)) := mvarId.withContext do
  let target ← mvarId.getType'
  let some (_, _, rhs) := target.eq? | return none
  let rec go (exceptions : Std.HashSet MatchToSplit) : MetaM (Option (List MVarId)) := do
    let some candidate ← findMatchToSplit? rhs declNames exceptions | return none
    let saved ← saveState
    try
      let branches ← Split.refineMatch mvarId candidate.declName candidate.levels candidate.params candidate.discrs
      let branches ← branches.mapM fun branch => do
        let normalized ← normalizeEqn branch
        if normalized == branch then
          throwError "case split did not reduce the right-hand side"
        return normalized
      return some branches
    catch ex =>
      saved.restore
      trace[Elab.definition.eqns] "cannot split {.ofConstName candidate.declName}\n{ex.toMessageData}"
      go (exceptions.insert candidate)
  go {}

/--
Calculates equation statements by normalizing the initial goal, recursively splitting eligible
matches, and saving terminal goals. Each recursive call receives an already-normalized RHS.
The resulting statements are proved separately by `mkEqnProof`.
-/
partial def mkEqnTypes (declNames : Array Name) (mvarId : MVarId) : MetaM (Array Expr) := do
  let (_, eqnTypes) ← go (← normalizeEqn mvarId) |>.run #[]
  return eqnTypes
where
  go (mvarId : MVarId) : StateRefT (Array Expr) MetaM Unit := do
    trace[Elab.definition.eqns] "mkEqnTypes step\n{MessageData.ofGoal mvarId}"
    if let some mvarIds ← splitMatch? mvarId declNames then
      mvarIds.forM go
    else
      saveEqn mvarId

/--
Removes parameters unused by both the equation's conclusion and its proof, retaining the
transitive type dependencies of the remaining parameters.
-/
def removeUnusedEqnHypotheses (declType declValue : Expr) : CoreM (Expr × Expr) := do
  go declType declValue #[] {}
where
  go (type value : Expr) (xs : Array Expr) (lctx : LocalContext) : CoreM (Expr × Expr) := do
    match value with
    | .lam n d b bi =>
      let d := d.instantiateRev xs
      let fvarId ← mkFreshFVarId
      go (type.bindingBody!) b (xs.push (mkFVar fvarId)) (lctx.mkLocalDecl fvarId n d bi)
    | _ =>
      let type  := type.instantiateRev xs
      let value := value.instantiateRev xs
      let mut s := collectFVars (collectFVars {} type) value
      let mut xsNew := #[]
      for x in xs.reverse do
        if s.fvarSet.contains x.fvarId! then
          s := collectFVars s (lctx.getFVar! x).type
          xsNew := xsNew.push x
      if xsNew.size == xs.size then
        return (declType, declValue)
      else
        xsNew := xsNew.reverse
        return (lctx.mkForall xsNew type, lctx.mkLambda xsNew value)


structure EqnTypesKey where
  declName : Name
  declNames : Array Name
deriving BEq, Hashable, TypeName

structure EqnTypes where
  types : Array Expr
deriving TypeName

def realizeEqnTypes (key : EqnTypesKey) : MetaM EqnTypes :=
  withEqnOptions key.declName <| withOptions (tactic.hygienic.set · false) do
    let target ← unfoldThmType key.declName
    let types ← withNewMCtxDepth <|
      forallTelescope (cleanupAnnotations := true) target fun _ target => do
        let goal ← mkFreshExprSyntheticOpaqueMVar target
        withReducible do
          mkEqnTypes key.declNames goal.mvarId!
    return { types }

def realizeEqn (declName name : Name) (type : Expr) : MetaM Unit :=
  withEqnOptions declName <| withOptions (tactic.hygienic.set · false) do
    let info ← getConstInfoDefn declName
    let value ← mkEqnProof declName type
    let (type, value) ← removeUnusedEqnHypotheses type value
    addDecl <| (←mkThmOrUnsafeDef {
      name, type, value
      levelParams := info.levelParams
    })
    inferDefEqAttr name

/--
Generate equations for `declName`.

This unfolds the function application on the LHS (using an unfold theorem, if present, or else by
delta-reduction), calculates the types for the equational theorems using `mkEqnTypes`, and then
proves them using `mkEqnProof`.
-/
def mkEqns (declName : Name) (declNames : Array Name) : MetaM (Array Name) := do
  trace[Elab.definition.eqns] "mkEqns: {.ofConstName declName}"
  -- The caller's options (e.g. `backward.isDefEq.respectTransparency`) can change how
  -- `mkEqnTypes` splits, so the types must not be computed in the caller's context.
  let key := { declName, declNames : EqnTypesKey }
  let { types := eqnTypes } ← realizeValue declName key (realizeEqnTypes key)
  let mut thmNames := #[]
  for h : i in *...eqnTypes.size do
    let type := eqnTypes[i]
    trace[Elab.definition.eqns] "eqnType[{i}]: {eqnTypes[i]}"
    let name := mkEqLikeNameFor (← getEnv) declName s!"{eqnThmSuffixBasePrefix}{i+1}"
    thmNames := thmNames.push name
    -- determinism: `type` comes from `realizeValue`, so it is independent of the environment
    -- changes since `declName` was added
    realizeConst declName name (realizeEqn declName name type)
  return thmNames

/--
Equation-theorem provider for definitions. Recursive definitions use split equations;
nonrecursive definitions use either split equations or one unfolding equation, according to
`backward.eqns.nonrecursive`.
-/
def getEqnsFor? (declName : Name) : MetaM (Option (Array Name)) := do
  if (← isRecursiveDefinition declName) then
    let some (.defnInfo info) := (← getEnv).find? declName |
      throwError "internal error: recursive definition `{declName}` is not a definition"
    let n ← mkEqns declName info.all.toArray
    return some n
  if (← getEnv).contains declName then
    if backward.eqns.nonrecursive.get (← getOptions) then
      mkEqns declName #[]
    else
      let eq1 := mkEqLikeNameFor (← getEnv) declName eqn1ThmSuffix
      let o ← mkSimpleEqThm declName eq1
      return o.map (#[·])
  else
    return none

builtin_initialize
  registerGetEqnsFn getEqnsFor?


end Lean.Elab.Eqns
