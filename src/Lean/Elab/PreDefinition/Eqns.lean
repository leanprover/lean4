/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Joachim Breitner
-/
module
prelude
import Lean.Elab.PreDefinition.EqnsUtils
import Lean.Meta.Match.NamedPatterns
import Lean.Meta.Tactic.Simp.Main
import Lean.Meta.Tactic.Split
import Lean.Meta.Tactic.SplitIf
import Lean.Meta.Tactic.CasesOnStuckLHS
import Lean.Meta.LetToHave

/-!
This module implements the generation of equational theorems, given unfolding theorems.
The unfolding theorems are generated differently for different kinds of recursive definition,
but the code here is no longer cares about that.

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

def lhsDependsOn (type : Expr) (fvarId : FVarId) : MetaM Bool :=
  forallTelescope type fun _ type => do
    if let some (_, lhs, _) ← matchEq? type then
      dependsOn lhs fvarId
    else
      dependsOn type fvarId

/--
  Eliminate `namedPatterns` from equation, and trivial hypotheses.
-/
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


/-- Zeta-reduces the `let`s in the binder prefix of `∀ xs, lhs = rhs`. -/
def zetaReduceLets (type : Expr) : MetaM Expr := do
  let mut e := type
  let mut subst := #[]
  let mut xs := #[]
  let mut lctx : LocalContext := {}
  repeat
    match e with
    | .forallE n d b bi =>
      let fvarId ← mkFreshFVarId
      lctx := lctx.mkLocalDecl fvarId n (d.instantiateRev subst) bi
      xs := xs.push (mkFVar fvarId)
      subst := subst.push (mkFVar fvarId)
      e := b
    | .letE _ _ v b _ =>
      subst := subst.push (v.instantiateRev subst)
      e := b
    | _ => break
  return lctx.mkForall xs (e.instantiateRev subst)

/--
Saves the equation type for the goal `mvarId`, whose target is `lhs = rhs`, where `mkEqnTypes`
stopped splitting. The equation abstracts the local declarations that the target depends on,
including through the types and values of other declarations, and the hypotheses about them that
the split produced (see `isIrrelevant`). See `mkEqnType` for how let-declarations are handled.
-/
partial def saveEqn (mvarId : MVarId) : StateRefT (Array Expr) MetaM Unit := mvarId.withContext do
  let target ← mvarId.getType'
  let fvarState := collectFVars {} target
  let fvarState ← (← getLCtx).foldrM (init := fvarState) fun decl fvarState => do
    if fvarState.fvarSet.contains decl.fvarId then
      -- We need to track `let`-declarations. `introRootLets` keeps them now.
      let fvarState := collectFVars fvarState (← instantiateMVars decl.type)
      let some value := decl.value? (allowNondep := true) | return fvarState
      return collectFVars fvarState (← instantiateMVars value)
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
  let type ← mkEqnType fvarIds target
  let type ← simpEqnType type
  modify (·.push type)
where
  /--
  Returns the equation type for the goal `target`, which is `lhs = rhs`, abstracting the local
  declarations `fvarIds` that the equation depends on, in context order. The let-declarations among
  `fvarIds`, which `introRootLets` introduced, become `have`s (or `let`s, if dependent) of the
  right-hand side: the result is `∀ xs, lhs = let ls := vs; rhs`, where the `xs` are the other
  declarations. A let-declaration that `lhs` or the type of some `x` depends on is zeta-reduced
  instead.

  For example, given
  ```
  n : Nat
  y : Nat := n + 1
  ⊢ f n = y * 2
  ```
  and `fvarIds := #[n, y]`, the result is
  ```
  ∀ n, f n =
    have y := n + 1
    y * 2
  ```
  If `fvarIds` also contains `h : y ≠ 0`, then `y` is zeta-reduced, and the result is
  ```
  ∀ n, n + 1 ≠ 0 → f n = (n + 1) * 2
  ```
  The alternative is a `let` among the binders, `∀ n, let y := n + 1; y ≠ 0 → f n = y * 2`, but
  `rw` and `simp` expect an equation lemma to be a telescope of `∀`s ending in an equation, with
  the left-hand side's arguments visible to them. Zeta-reducing is rarely needed: the hypotheses of a
  split are about the discriminants, which are variables of the left-hand side, not about `have`s.
  -/
  mkEqnType (fvarIds : Array FVarId) (target : Expr) : MetaM Expr := do
    let isLet (fvarId : FVarId) : MetaM Bool := return (← fvarId.getDecl).isLet
    if (← fvarIds.allM fun x => notM (isLet x)) then
      mkForallFVars (fvarIds.map mkFVar) target
    else
      let some (_, lhs, rhs) := target.eq?
        | zetaReduceLets (← mkForallFVars (fvarIds.map mkFVar) target)
      -- `outer` is closed under dependencies: it contains the lets that `lhs`, the type of a
      -- non-let, or the value of an `outer` let depends on.
      -- All variables in `outer` are inlined.
      -- A declaration's dependencies come before it in `fvarIds`, so one reverse pass suffices.
      let mut outer : FVarIdSet := {}
      let mut need := collectFVars {} (← instantiateMVars lhs)
      for fvarId in fvarIds.reverse do
        let decl ← fvarId.getDecl
        if decl.isLet then
          if need.fvarSet.contains fvarId then
            outer := outer.insert fvarId
            need := collectFVars need (← instantiateMVars decl.value)
        else
          need := collectFVars need (← instantiateMVars decl.type)
      let mut xs := #[]
      let mut ls := #[]
      for fvarId in fvarIds do
        if (← isLet fvarId) && !outer.contains fvarId then
          ls := ls.push (mkFVar fvarId)
        else
          xs := xs.push (mkFVar fvarId)
      let rhs ← mkLetFVars ls rhs (generalizeNondepLet := false)
      -- `intro` turns a `have` into a dependent let-declaration, so we restore the `have`s.
      let rhs ← if (← getOptions).getBool `cleanup.letToHave true then letToHave rhs else pure rhs
      zetaReduceLets (← mkForallFVars xs (← mkEq lhs rhs) (generalizeNondepLet := false))

  /--
    We say the type/proposition is "irrelevant" if
    1- It does not contain any variable in `fvarIdSet` OR
    2- It is of the form `x = t` or `t = x` where `x` is a free variable
       that is not in `fvarIdSet`. This can of equality can be eliminated by substitution.  -/
  isIrrelevant (fvarIdSet : FVarIdSet) (type : Expr) : MetaM Bool := do
    if Option.isNone <| type.find? fun e => e.isFVar && fvarIdSet.contains e.fvarId! then
      return true
    else if let some (_, lhs, rhs) := type.eq? then
      return (lhs.isFVar && !fvarIdSet.contains lhs.fvarId!)
             || (rhs.isFVar && !fvarIdSet.contains rhs.fvarId!)
    else
      return false

  pushDecl (fvarIdSet : FVarIdSet) (fvarIds : Array FVarId) (localDecl : LocalDecl) : MetaM (FVarIdSet × Array FVarId) := do
    let (fvarIdSet, fvarIds) ← collectDeps fvarIdSet fvarIds (← instantiateMVars localDecl.type)
    let (fvarIdSet, fvarIds) ← match localDecl.value? (allowNondep := true) with
      | some value => collectDeps fvarIdSet fvarIds (← instantiateMVars value)
      | none => pure (fvarIdSet, fvarIds)
    return (fvarIdSet.insert localDecl.fvarId, fvarIds.push localDecl.fvarId)

  collectDeps (fvarIdSet : FVarIdSet) (fvarIds : Array FVarId) (type : Expr) : MetaM (FVarIdSet × Array FVarId) := do
    let s := collectFVars {} type
    let usedFVarIds ← sortFVarIds <| s.fvarSet.toArray
    let mut fvarIdSet := fvarIdSet
    let mut fvarIds := fvarIds
    for fvarId in usedFVarIds do
      unless fvarIdSet.contains fvarId do
        (fvarIdSet, fvarIds) ← pushDecl fvarIdSet fvarIds (← fvarId.getDecl)
    return (fvarIdSet, fvarIds)

/-- Zeta-reduces the `let`s and `have`s at the root of `e`, and consumes metadata. -/
partial def expand (e : Expr) : Expr := Id.run do
  let mut e := e
  let mut subst := #[]
  repeat
    match e with
    | .letE _ _ v b _ =>
      subst := subst.push (v.instantiateRev subst)
      e := b
    | .mdata _ b => e := b
    | _ => break
  let r := e.instantiateRev subst
  -- The substitution may expose another root `let`, as in `let y := (let z := x; t); y`.
  if r.isLet || r.isMData then expand r else r


/--
Follows a chain of let-variables to the first value that is not one.

`introRootLets` keeps the `let`s and `have`s of the right-hand side as let-declarations, so a
`match` discriminant may be a let-variable that stands for a variable or a constructor application.
We use this function to decide whether such a discriminant is a variable, which `match` can be
split on, or a constructor application, which `match` can be reduced on.

For example, given
```
x : Nat
y : Option Nat := some x
z : Option Nat := y
⊢ f x = match z with
  | some n => n
  | none => 0
```
`resolveLetVar letValue? z` is `some x`, so the `match` reduces to `x`.
-/
partial def resolveLetVar (letValue? : FVarId → Option Expr) (e : Expr) : Expr :=
  if let .fvar fvarId := e then
    match letValue? fvarId with
    | some v => resolveLetVar letValue? v
    | none => e
  else
    e

/--
  Quick filter for deciding whether to use `simpMatch?` at `mkEqnTypes`.
  If the result is `false`, then it is not worth trying `simpMatch`.
-/
def shouldUseSimpMatch (e : Expr) (letValue? : FVarId → Option Expr := fun _ => none) : MetaM Bool := do
  let env ← getEnv
  let find (root : Expr) : ExceptT Unit MetaM Unit :=
    root.forEach fun e => do
      if let some info := isMatcherAppCore? env e then
        let args := e.getAppArgs
        for discr in args[info.getFirstDiscrPos...(info.getFirstDiscrPos + info.numDiscrs)] do
          if (← Meta.isConstructorApp (resolveLetVar letValue? discr)) then
            throwThe Unit ()
  return (← (find e).run) matches .error _

/--
Finds a `match` to split in `e`, the first one in a pre-order traversal. Returns `(m, none)` if the
`match` `m` occurs in `e`, and `(m, some x)` if it occurs in the value of the let-variable `x`.

- `declNames`: the functions being defined, empty for a non-recursive definition. For a recursive
  definition, unless `deepRecursiveSplit` is set, only a `match` with an alternative that has a
  recursive call is split.
- `exceptionSet`: the `match`es to skip, because splitting them already failed.
- `letValue?`: the value of a let-variable, used to decide whether a discriminant that is a
  let-variable stands for a variable (see `resolveLetVar`). A `match` is only split if one of its
  discriminants is a variable.
- `letMatch?`: the `match` to split in the value of a let-variable, if any. The search treats an
  occurrence of a let-variable `x` as an occurrence of its value: if `letMatch? x` is `some m`, the
  search stops at `x` and returns `(m, some x)`. This finds the same `match`, in the same order, as
  a search in `e` with its let-variables zeta-reduced.

  `letMatch?` memoizes this function on the let-values: `mkLetMatches` calls it on the value of
  each let-declaration, in context order, passing the results for the earlier ones. `splitMatch?`
  then calls it on the target with all results. This way each value is searched once, instead of
  at each occurrence of its let-variable.
-/
def findMatchToSplit? (deepRecursiveSplit : Bool) (env : Environment) (e : Expr)
    (declNames : Array Name) (exceptionSet : ExprSet) (letValue? : FVarId → Option Expr := fun _ => none)
    (letMatch? : FVarId → Option Expr := fun _ => none) : Option (Expr × Option FVarId) :=
  let r? := e.findExt? fun e => Id.run do
    if let .fvar fvarId := e then
      return if (letMatch? fvarId).isSome then .found else .done
    if e.hasLooseBVars || exceptionSet.contains e then
      return Expr.FindStep.visit
    else if let some info := isMatcherAppCore? env e then
      let args := e.getAppArgs
      -- If none of the discriminants is a free variable, then it is not worth splitting the match
      let mut hasFVarDiscr := false
      for i in info.getFirstDiscrPos...(info.getFirstDiscrPos + info.numDiscrs) do
        let discr := args[i]!
        if (resolveLetVar letValue? discr).isFVar then
          hasFVarDiscr := true
          break
      unless hasFVarDiscr do
        return Expr.FindStep.visit
      -- For non-recursive functions (`declNames` empty), we split here
      if declNames.isEmpty then
          return Expr.FindStep.found
      -- For recursive functions, the “new” behavior is to likewise split
      if deepRecursiveSplit then
          return Expr.FindStep.found
      -- Else, the “old” behavior is split only when at least one alternative contains a `declNames`
      -- application with loose bound variables.
      for i in info.getFirstAltPos...(info.getFirstAltPos + info.numAlts) do
        let alt := args[i]!
        if Option.isSome <| alt.find? fun e => declNames.any e.isAppOf && e.hasLooseBVars then
          return Expr.FindStep.found
      return Expr.FindStep.visit
    else
      let Expr.const declName .. := e.getAppFn | return Expr.FindStep.visit
      if declName == ``WellFounded.fix || isBRecOnRecursor env declName then
        -- We should not go inside unfolded nested recursive applications
        return Expr.FindStep.done
      else
        return Expr.FindStep.visit
  match r? with
  | some (.fvar fvarId) => (letMatch? fvarId).map (·, some fvarId)
  | some e => some (e, none)
  | none => none

/--
Returns the value of `fvarId` if it is a let-variable in `lctx`, and `none` otherwise. Nondependent
let-declarations (`have`s) are included. Partially applied to `lctx`, it is the `letValue?`
argument of the pure functions `findMatchToSplit?` and `resolveLetVar`, which cannot access the
local context.
-/
def letValueIn (lctx : LocalContext) (fvarId : FVarId) : Option Expr :=
  (lctx.find? fvarId).bind (·.value? (allowNondep := true))

/-- `letValueIn` for the local context of `mvarId`. -/
def _root_.Lean.MVarId.letValueIn (mvarId : MVarId) : MetaM (FVarId → Option Expr) :=
  return Eqns.letValueIn (← mvarId.getDecl).lctx

/-- The discriminants of the `match` application `e` that are let-variables according to `letValue?`. -/
def letVarDiscrs (env : Environment) (letValue? : FVarId → Option Expr) (e : Expr) : Array FVarId := Id.run do
  let some info := isMatcherAppCore? env e | return #[]
  let mut fvarIds := #[]
  for discr in e.getAppArgs[info.getFirstDiscrPos...(info.getFirstDiscrPos + info.numDiscrs)] do
    if let .fvar fvarId := discr then
      if (letValue? fvarId).isSome then
        fvarIds := fvarIds.push fvarId
  return fvarIds

/-- The let-declarations that the target depends on, in context order. -/
def usedLetDecls (mvarId : MVarId) : MetaM (Array LocalDecl) := mvarId.withContext do
  let lctx ← getLCtx
  unless lctx.any (·.isLet) do return #[]
  let used := collectFVars {} (← instantiateMVars (← mvarId.getType))
  -- A declaration precedes the ones that depend on it, so one reverse pass suffices.
  let (_, decls) ← lctx.foldrM (init := (used, #[])) fun decl (used, decls) => do
    let some v := decl.value? (allowNondep := true) | return (used, decls)
    if used.fvarSet.contains decl.fvarId then
      return (collectFVars used (← instantiateMVars v), decls.push decl)
    else
      return (used, decls)
  return decls.reverse

/--
Returns the map `letMatch?` for `findMatchToSplit?`: for each let-declaration `x` in `decls` whose
value has a `match` to split, maps `x` to the first such `match`, as found by `findMatchToSplit?`
on the value. The other arguments are passed to `findMatchToSplit?`.

`decls` must be in context order, since the search in the value of `x` uses the results for the
let-declarations before `x`: if the value of `x` mentions `y`, and the value of `y` has a `match`
to split, then `x` is mapped to that `match`.

Each `x` is also mapped to the let-declaration whose value has the `match`, which `splitMatch?`
moves back into the right-hand side to split it. For example, given
```
x : Nat
a : Nat := match x with
  | 0 => 1
  | _ + 1 => 2
c : Nat := a + a
```
both `a` and `c` are mapped to the `match` in the value of `a`, and to `a`.
-/
def mkLetMatches (deep : Bool) (env : Environment) (declNames : Array Name) (exceptionSet : ExprSet)
    (letValue? : FVarId → Option Expr) (decls : Array LocalDecl) :
    MetaM (FVarIdMap (Expr × FVarId)) := do
  let mut letMatches : FVarIdMap (Expr × FVarId) := {}
  for decl in decls do
    -- The `match` may be below `let`s at the root of the value.
    let v := expand (← instantiateMVars decl.value)
    let letMatch? := fun fvarId => (letMatches.get? fvarId).map (·.1)
    if let some (e, y?) := findMatchToSplit? deep env v declNames exceptionSet letValue? letMatch? then
      let owner := match y? with
        | some y => (letMatches.get? y).get!.2
        | none => decl.fvarId
      letMatches := letMatches.insert decl.fvarId (e, owner)
  return letMatches

/--
Moves the let-declarations `fvarIds`, and the let-declarations that depend on them, from the local
context back into the right-hand side: the target `lhs = rhs` becomes `lhs = let xs := vs; rhs`.
There, `Split.splitMatch` and `simpMatch?` rewrite the values `vs`, using the hypotheses of a split.
A moved value `v` becomes `expand v`, so that a `match` below the `let`s at the root of `v` has no
loose bound variables. Returns `none` if `lhs` or a declaration that is not a let-declaration
depends on them.
-/
def moveLetsToRHS? (mvarId : MVarId) (fvarIds : Array FVarId) : MetaM (Option MVarId) :=
  mvarId.withContext do
    let target ← mvarId.getType'
    let some (_, lhs, rhs) := target.eq? | return none
    let mut lctx ← getLCtx
    let mut moved : FVarIdSet := {}
    let mut xs := #[]
    for decl in (← getLCtx) do
      let mut dep := fvarIds.contains decl.fvarId
      unless dep do
        dep := (← instantiateMVars decl.type).hasAnyFVar moved.contains
        if let some v := decl.value? (allowNondep := true) then
          dep := dep || (← instantiateMVars v).hasAnyFVar moved.contains
      unless dep do continue
      let some v := decl.value? (allowNondep := true) | return none
      moved := moved.insert decl.fvarId
      xs := xs.push (mkFVar decl.fvarId)
      lctx := lctx.modifyLocalDecl decl.fvarId (·.setValue (expand (← instantiateMVars v)))
    if xs.isEmpty || (← instantiateMVars lhs).hasAnyFVar moved.contains then return none
    let rhs ← withLCtx lctx (← getLocalInstances) do
      mkLetFVars xs rhs (generalizeNondepLet := false)
    let target ← mkEq lhs rhs
    let lctxNew := xs.foldr (init := lctx) fun x lctx => lctx.erase x.fvarId!
    let mvarNew ← mkFreshExprMVarAt lctxNew (← getLocalInstances) target .syntheticOpaque
      (← mvarId.getTag)
    mvarId.assign mvarNew
    return some mvarNew.mvarId!

partial def splitMatch? (mvarId : MVarId) (declNames : Array Name) : MetaM (Option (List MVarId)) := commitWhenSome? do
  let target ← mvarId.getType'
  let letValue? ← mvarId.letValueIn
  let decls ← usedLetDecls mvarId
  let deep := backward.eqns.deepRecursiveSplit.get (← getOptions)
  let env ← getEnv
  let rec go (badCases : ExprSet) : MetaM (Option (List MVarId)) := do
    let letMatches ← mkLetMatches deep env declNames badCases letValue? decls
    if let some (e, fvarId?) := findMatchToSplit? deep env target declNames badCases letValue?
        (fun fvarId => (letMatches.get? fvarId).map (·.1)) then
      -- `splitMatch` may assign `mvarId` before failing.
      let saved ← saveState
      try
        match fvarId? with
        | some fvarId =>
          -- `e` is in the value of `owner`, which we move back into the right-hand side.
          let some (_, owner) := letMatches.get? fvarId | unreachable!
          let some mvarId' ← moveLetsToRHS? mvarId #[owner]
            | throwError "cannot move let-declaration to the right-hand side"
          Meta.Split.splitMatch mvarId' e
        | none => Meta.Split.splitMatch mvarId e
      catch ex =>
        saved.restore
        trace[Elab.definition.eqns] "cannot split {e}\n{ex.toMessageData}"
        -- Splitting another `match` first may make `e` splittable, as for a `match` whose
        -- discriminants include let-variables that depend on a variable split by the other one.
        if let some mvarIds ← go (badCases.insert e) then
          return some mvarIds
        -- Otherwise, we zeta-reduce, which is the last resort since it copies values.
        if let some fvarId := fvarId? then
          return some [← mvarId.replaceTargetDefEq (← zetaDeltaFVars target #[fvarId])]
        let fvarIds := letVarDiscrs (← getEnv) letValue? e
        if fvarIds.isEmpty then
          return none
        let target' ← mvarId.withContext <| zetaDeltaFVars target fvarIds
        commitWhenSome? do splitMatch? (← mvarId.replaceTargetDefEq target') declNames
    else
      trace[Elab.definition.eqns] "did not find term to split\n{MessageData.ofGoal mvarId}"
      return none
  go {}

/--
Returns `true` if `simpMatch?` reduces the `match` application `e` itself. This is the step that
`Split.simpMatch` applies to each `match`, but applied only to `e`, without simplifying its
subterms.
-/
def reducesMatch (e : Expr) : MetaM Bool := do
  if (← reduceRecMatcher? e).isSome then return true
  let some matcherName := e.getAppFn.constName? | return false
  let methods : Simp.Methods := { discharge? := (← SplitIf.mkDischarge?) }
  let (step, _) ← Simp.SimpM.run (← Split.getSimpMatchContext) (methods := methods)
    (k := Simp.simpMatchCore matcherName e)
  return !(step matches .continue)

/--
Replaces each `match` discriminant that is a let-variable whose value is a constructor application
with that value, so that `simpMatch?` can reduce the `match`. Other occurrences of the
let-variable are kept. The discriminants of a `match` are only replaced if the `match` then
reduces, so that a value is not copied into a `match` that stays, as `big` below:
```
x w : Nat
big : Option Nat := some (x * x)
y : Option Nat := some x
⊢ f x w = (match y with | some n => n | none => 0) + (match g w, big with ...)
```
Here `y` is replaced, and `big` is not, since `g w` is not a constructor application.
-/
def inlineCtorLetDiscrs? (mvarId : MVarId) : MetaM (Option MVarId) := mvarId.withContext do
  unless (← getLCtx).any (·.isLet) do return none
  let target ← mvarId.getType'
  let letValue? ← mvarId.letValueIn
  let env ← getEnv
  let post (e : Expr) : MetaM TransformStep := do
    let some info := isMatcherAppCore? env e | return .done e
    let mut args := e.getAppArgs
    let mut modified := false
    for i in info.getFirstDiscrPos...(info.getFirstDiscrPos + info.numDiscrs) do
      let discr := args[i]!
      unless discr.isFVar && (letValue? discr.fvarId!).isSome do continue
      let v := resolveLetVar letValue? discr
      if (← isConstructorApp v) then
        args := args.set! i v
        modified := true
    unless modified do return .done e
    let e' := mkAppN e.getAppFn args
    if (← reducesMatch e') then
      return .done e'
    else
      return .done e
  -- `Meta.transform`, since `reducesMatch` needs a term without loose bound variables.
  let target' ← Meta.transform target (post := post)
  if target' == target then return none
  return some (← mvarId.replaceTargetDefEq target')

/-- Applies `inlineCtorLetDiscrs?` only if `simpMatch?` then reduces the `match`. -/
def simpCtorLetDiscrs? (mvarId : MVarId) : MetaM (Option MVarId) := commitWhenSome? do
  let some mvarId ← inlineCtorLetDiscrs? mvarId | return none
  simpMatch? mvarId

/--
Introduces the `let`s and `have`s at the root of the right-hand side as let-declarations, so that a
`match` below them can be split while the equations keep them instead of copying their values into
each use. Also consumes metadata.
-/
def introRootLets (mvarId : MVarId) : MetaM MVarId := mvarId.withContext do
  let target ← mvarId.getType'
  let some (_, lhs, rhs) := target.eq? | return mvarId
  if !rhs.isLet && !rhs.isMData then return mvarId
  let mut lctx ← getLCtx
  let mut fvars := #[]
  let mut e := rhs
  repeat
    match e with
    | .mdata _ b => e := b
    | .letE n t v b _ =>
      let fvarId ← mkFreshFVarId
      lctx := lctx.mkLetDecl fvarId n (t.instantiateRev fvars) (v.instantiateRev fvars)
      fvars := fvars.push (mkFVar fvarId)
      e := b
    | _ => break
  let newMVar ← mkFreshExprMVarAt lctx (← getLocalInstances) (← mkEq lhs (e.instantiateRev fvars)) .syntheticOpaque (← mvarId.getTag)
  mvarId.assign (← withLCtx lctx {} (mkLetFVars fvars newMVar))
  return newMVar.mvarId!

/--
Simplifies the `match`es with constructor discriminants in the values of the let-declarations that
the target depends on. A split creates such `match`es by substituting a constructor for a variable
in a value. The declarations are moved back into the right-hand side, where `simpMatch?` rewrites
them, as for the declaration `y` in
```
n : Nat
y : Nat := match n + 1 with
  | 0 => 1
  | m + 1 => m
⊢ f (n + 1) = y + y
```
which becomes
```
n : Nat
⊢ f (n + 1) = have y := n; y + y
```
-/
def simpLetValues? (mvarId : MVarId) : MetaM (Option MVarId) := commitWhenSome? do
  mvarId.withContext do
    let decls ← usedLetDecls mvarId
    if decls.isEmpty then return none
    let letValue? ← mvarId.letValueIn
    let fvarIds ← decls.filterMapM fun decl => do
      let v := expand (← instantiateMVars decl.value)
      return if ← shouldUseSimpMatch v letValue? then some decl.fvarId else none
    if fvarIds.isEmpty then return none
    let some mvarId ← moveLetsToRHS? mvarId fvarIds | return none
    simpMatch? mvarId

/-- Simplifies or splits a `match` of the right-hand side. Commits only if this makes progress. -/
def tryStep? (mvarId : MVarId) (declNames : Array Name) : MetaM (Option (List MVarId)) :=
  commitWhenSome? do
    if let some mvarId ← simpLetValues? mvarId then
      return some [mvarId]
    if let some mvarId ← simpCtorLetDiscrs? mvarId then
      return some [mvarId]
    if (← shouldUseSimpMatch (← mvarId.getType')) then
      if let some mvarId ← simpMatch? mvarId then
        return some [mvarId]
    splitMatch? mvarId declNames

partial def mkEqnTypes (declNames : Array Name) (mvarId : MVarId) : MetaM (Array Expr) := do
  let (_, eqnTypes) ← go mvarId |>.run #[]
  return eqnTypes
where
  go (mvarId : MVarId) : StateRefT (Array Expr) MetaM Unit := do
    trace[Elab.definition.eqns] "mkEqnTypes step\n{MessageData.ofGoal mvarId}"
    -- `saveEqn` only puts back the let-declarations that the equation uses, so the unused root
    -- `let`s and `have`s are dropped.
    let mvarId ← introRootLets mvarId
    if let some mvarIds ← tryStep? mvarId declNames then
      mvarIds.forM go
    else
      saveEqn mvarId

/--
  Some of the hypotheses added by `mkEqnTypes` may not be used by the actual proof (i.e., `value` argument).
  This method eliminates them.

  Alternative solution: improve `saveEqn` and make sure it never includes unnecessary hypotheses.
  These hypotheses are leftovers from tactics such as `splitMatch?` used in `mkEqnTypes`.
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
