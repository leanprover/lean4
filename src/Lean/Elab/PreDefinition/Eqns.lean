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
import Lean.Meta.Tactic.Contradiction
import Lean.Meta.Tactic.Refl
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
unfolding theorem `declName.eq_def` when available and delta reduction otherwise.

The unfolding theorem is used for nonrecursive definitions too. Delta reduction is cheap here, but
the proof it produces can be expensive for the kernel. Given the goal `f a = rhs`, it produces
`id (f a = rhs) h` where `h : body[a] = rhs`. This term only claims that `f a` and `body[a]` are
definitionally equal. It does not record that the step was "unfold `f` once", and the kernel has to
rediscover it with its own unfolding heuristics.

Example: `f` is defined by a `match` on `String` literals, and `a` is the literal `"lit"`.
The kernel has to check `f "lit" =?= f.match_1 .. "lit" ..`.
1. `f.match_1` has `abbrev` reducibility hints, so the kernel unfolds it before `f`, and obtains
   `dite ("lit" = "lit_0") ..`.
2. If `f` and `dite` have the same definitional height, the kernel unfolds both.
3. Unfolding `dite` exposes `Decidable.rec`, and the kernel evaluates `String.decEq "lit" "lit_0"`
   to select a branch. The other side is `f.match_1 .. "lit" ..` again.
4. The two sides never become syntactically equal, and the kernel evaluates the `match` down to the
   alternative for `"lit"`.

So, the kernel evaluates the whole `match` to check each equation theorem. This cost is not
visible to `maxHeartbeats`.

The proof `f.eq_def a` has type `f a = body[a]`, and the kernel has nothing to rediscover.
The definitional step is checked only once, at `f.eq_def`, where the discriminant is a variable and
the `match` cannot be evaluated.
-/
def unfoldLHS (declName : Name) (mvarId : MVarId) : MetaM MVarId := mvarId.withContext do
  if let some unfoldThm ← getUnfoldEqnFor? declName (nonRec := true) then
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
    deltaLHS mvarId

/--
Rewrites the matcher application `e` using the congruence equation of the first alternative that
applies. Returns `none` if no alternative applies. Arguments of `e` beyond the arity of the
matcher are applied to the result.

Example: the matcher application
```
match "b" with
| "a" => 1
| "b" => 2
| _ => 3
```
is rewritten to `2` using the congruence equation of the second alternative
```
congr_eq_2 : ∀ motive x h_1 h_2 h_3, x = "b" →
  (match x with | "a" => h_1 () | "b" => h_2 () | _ => h_3 x) ≍ h_2 ()
```

The alternatives are tried in order with `rwMatcher`. To try an alternative, `rwMatcher`
instantiates its congruence equation, and proves each hypothesis `discr = pattern` by reflexivity
or by assumption. In the example, the first alternative does not apply because `"b" = "a"` cannot
be proved, and the second one applies because `"b" = "b"` is proved by reflexivity.

An attempt is expensive when the matcher has many alternatives: the congruence equation has one
argument for each of them. For a `match` with `n` literal alternatives, the equation of the last
one would need `n` attempts. So, an alternative is skipped, without trying it, when the attempt
is known to fail:
1. a discriminant and the corresponding pattern are different literals (see `litValue?`), so the
   hypothesis `discr = pattern` cannot be proved by reflexivity, and
2. the local context has no hypotheses (see `hasHyp`), so it cannot be proved by assumption.

In the example, the first alternative is skipped if the local context has no hypotheses.
If it contains `h : "b" = "a"`, the first alternative is tried, and it applies.
-/
def rwMatcherApp? (e : Expr) : MetaM (Option Simp.Result) := do
  let some app ← matchMatcherApp? e | return none
  let f := { app with remaining := #[] }.toExpr
  let discrLits ← app.discrs.mapM litValue?
  let altLits ←
    if !discrLits.any (·.isSome) then pure #[]
    else if (← hasHyp) then pure #[]
    else getAltLits app
  for i in *...app.numAlts do
    if let some patLits := altLits[i]? then
      if isDifferent discrLits patLits then continue
    let r ← rwMatcher i f
    if r.expr != f then
      return some (← r.addExtraArgs app.remaining)
  return none
where
  /-- Returns `true` if `n` is a `Nat` numeral. -/
  isNumeral (n : Expr) : Bool := n.isRawNatLit || n.nat?.isSome

  /--
  Returns `true` if `e` has the shape of a literal supported by `litValue?`, and recognizing it
  does not require evaluating its type: the type is a constant, or `Fin n` or `BitVec n` where
  `n` is a numeral.
  -/
  isLitCandidate (e : Expr) : Bool :=
    match_expr e with
    | OfNat.ofNat type _ _ =>
      match_expr type with
      | Nat => true | Int => true
      | UInt8 => true | UInt16 => true | UInt32 => true | UInt64 => true
      | Fin n => isNumeral n
      | BitVec n => isNumeral n
      | _ => false
    | Neg.neg type _ _ => type.isConstOf ``Int
    | Char.ofNat _ => true
    | BitVec.ofNat n _ => isNumeral n
    | _ => false

  /--
  Returns `e` if it is a literal in its standard representation: a `String` literal, or a numeral
  or character of type `Nat`, `Int`, `Char`, `UInt8`, `UInt16`, `UInt32`, `UInt64`, `Fin n`, or
  `BitVec n`. Two such literals of the same type denote different values if and only if they are
  structurally different.

  The standard representation is the one `normLitValue` produces. A literal that is not in its
  standard representation is not accepted. For example, `(5 : UInt8)` elaborated using a local
  instance of `OfNat UInt8 5`: the functions that recognize literals do not inspect the instance,
  and this term may denote a number different from `5`.

  `e` is first checked with `isLitCandidate`, because these functions reduce the type of `e`. For
  example, they evaluate `n` in `BitVec n`.
  `Float` and `Float32` literals are not supported: `5` and `5.0` denote the same value, and
  `normLitValue` does not change them.
  -/
  litValue? (e : Expr) : MetaM (Option Expr) := do
    if e.isStringLit then return some e
    unless isLitCandidate e do return none
    unless (← isMatchValue e) do return none
    if (← normLitValue e) == e then return some e else return none

  /--
  Returns `true` if the local context may contain a hypothesis: a local declaration whose type is
  a proposition, or is in a universe that may be `Prop`.
  A hypothesis may prove `discr = pattern` by assumption even if `discr` and `pattern` are
  different literals, because the local context may be inconsistent. Only the universe of each
  type is inspected: comparing a type with `discr = pattern` may unfold definitions and use
  unification hints.
  -/
  hasHyp : MetaM Bool := do
    -- The most recent declarations are visited first, as `assumption` does.
    let hyp? ← (← getLCtx).findDeclRevM? fun localDecl => do
      if localDecl.isImplementationDetail then return none
      let .sort u ← instantiateMVars (← inferType localDecl.type) | return some ()
      if u.isNeverZero then return none else return some ()
    return hyp?.isSome

  /-- Returns, for each alternative of the matcher, the literals (see `litValue?`) in its patterns. -/
  getAltLits (app : MatcherApp) : MetaM (Array (Array (Option Expr))) := do
    let mut type := (← getConstVal app.matcherName).type
    for _ in *...(app.numParams + 1 + app.numDiscrs) do
      let .forallE _ _ b _ := type | return #[]
      type := b
    let mut altLits := #[]
    for _ in *...app.numAlts do
      let .forallE _ d b _ := type | return #[]
      -- The type of an alternative is `∀ fields, motive patterns`.
      altLits := altLits.push (← d.getForallBody.getAppArgs.mapM litValue?)
      type := b
    return altLits

  /-- Returns `true` if a discriminant and the corresponding pattern are different literals. -/
  isDifferent (discrLits patLits : Array (Option Expr)) : Bool := Id.run do
    for discrLit? in discrLits, patLit? in patLits do
      let some discrLit := discrLit? | continue
      let some patLit := patLit? | continue
      if discrLit != patLit then return true
    return false

/--
Rewrites a matcher application on the left-hand side of an equality goal with `rwMatcherApp?`.
Equation statements are computed with the same rewrite, so it proves equations whose
discriminants are not constructor applications.
-/
def rwMatcherLHS? (mvarId : MVarId) : MetaM (Option MVarId) := mvarId.withContext do
  let target ← mvarId.getType'
  let some (_, lhs, rhs) := target.eq? | return none
  let some r ← rwMatcherApp? lhs | return none
  let targetNew ← mkEq r.expr rhs
  let some proof := r.proof? | return some (← mvarId.replaceTargetDefEq targetNew)
  let mvarNew ← mkFreshExprSyntheticOpaqueMVar targetNew
  mvarId.assign (← mkEqTrans proof mvarNew)
  return some mvarNew.mvarId!

/--
Unifies the hypotheses `discr = pattern` and `discr ≍ pattern` that splitting a matcher leaves in
a branch when a discriminant is not a variable. The hypotheses considered are `a = b` where
neither `a` nor `b` is a variable, and `a ≍ b` where the types of `a` and `b` are definitionally
equal. Each one is unified as `cases` does: it is removed if the two sides are definitionally
equal, a variable is substituted, and applications of the same constructor are replaced by the
equalities between the fields. A hypothesis that cannot be unified is kept.
Returns `none` if a hypothesis equates different constructors or literals: the branch is closed.
-/
partial def unifyDiscrEqs (mvarId : MVarId) : MetaM (Option MVarId) := mvarId.withContext do
  for decl in (← getLCtx) do
    if decl.isImplementationDetail then continue
    if let some (_, a, b) := decl.type.eq? then
      if a.isFVar || b.isFVar then continue
    else if let some (α, _, β, _) := decl.type.heq? then
      unless (← isDefEq α β) do continue
    else
      continue
    let saved ← saveState
    let r? ← try
        let some r ← unifyEq? mvarId decl.fvarId | return none -- Goal closed, done.
        pure (some (← Cases.unifyEqs? r.numNewEqs r.mvarId r.subst))
      catch _ =>
        saved.restore
        pure none
    match r? with
    | none => continue -- Caught exception, keep traversing lctx
    | some none => return none -- Goal closed, done.
    | some (some (mvarId, _)) => return (← unifyDiscrEqs mvarId) -- Subgoal generated, continue from there
  return some mvarId

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
    let rfl : MetaM Unit := do
      unless (← tryURefl mvarId #[declName]) do throwError "`rfl` failed"
      trace[Elab.definition.eqns] "proved directly by rfl"
    reflOrProve rfl do go (← unfoldLHS declName mvarId)
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
    let rfl : MetaM Unit := do
      unless (← tryURefl mvarId) do throwError "`rfl` failed"
    reflOrProve rfl do
      if (← tryContradiction mvarId) then
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
            (← mvarIds.filterMapM unifyDiscrEqs).forM go
          else if let some mvarId ← rwMatcherLHS? mvarId then
            go mvarId
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
  if ← isMatcherApp e then
    if let some e' ← reduceRecMatcher? e then
      return .visit { expr := e' }
    if let some r ← rwMatcherApp? e then
      return .visit r
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
provides traversal and congruence. Congruence proofs are built in place, so normalization adds no
`congr_simp` theorems to the environment. Propositional RHS rewrites are lifted to the whole target;
definitional rewrites directly replace the target.
Returns the original goal when unchanged, which lets `splitMatch?` detect normalization progress.
-/
def normalizeEqn (mvarId : MVarId) : MetaM MVarId := mvarId.withContext do
  let target ← mvarId.getType'
  let some (_, lhs, rhs) := target.eq? | return mvarId
  let ctx ← Simp.mkContext
    (config := { Simp.neutralConfig with dsimp := true, etaStruct := .none, congrConsts := false })
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
      let branches ←
        if candidate.discrs.all (·.isFVar) then pure branches
        else branches.filterMapM fun branch => do
          let some branch ← unifyDiscrEqs branch | return none
          if (← branch.contradictionCore { useDecide := false, emptyType := false, genDiseq := true }) then return none
          return some branch
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
The body of a definition can mention private auxiliary proofs even if the equations are public,
so the statements are computed with private declarations visible.
-/
partial def mkEqnTypes (declNames : Array Name) (mvarId : MVarId) : MetaM (Array Expr) :=
  withoutExporting do
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


/--
Adds all equations for `declName`. The types are computed here so that they do not depend on the
caller's options (e.g. `backward.isDefEq.respectTransparency` can change how `mkEqnTypes` splits).
They can also mention constants realized during that computation, such as match equations in cast
proofs, so the theorems must be added in the same realization.
-/
def realizeEqns (declName : Name) (declNames : Array Name) : MetaM Unit :=
  withEqnOptions declName <| withOptions (tactic.hygienic.set · false) do
    let info ← getConstInfoDefn declName
    let target ← unfoldThmType declName
    let types ← withNewMCtxDepth <|
      forallTelescope (cleanupAnnotations := true) target fun _ target => do
        let goal ← mkFreshExprSyntheticOpaqueMVar target
        withReducible do
          mkEqnTypes declNames goal.mvarId!
    -- Splitting leaves no goals if the body eliminates an empty type.
    let types := if types.isEmpty then #[target] else types
    for h : i in *...types.size do
      let type := types[i]
      trace[Elab.definition.eqns] "eqnType[{i}]: {type}"
      let name := mkEqLikeNameFor (← getEnv) declName s!"{eqnThmSuffixBasePrefix}{i+1}"
      withDeclNameForAuxNaming name do
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
  let eq1 := mkEqLikeNameFor (← getEnv) declName eqn1ThmSuffix
  realizeConst declName eq1 (realizeEqns declName declNames)
  let some thmNames ← alreadyGenerated? declName |
    throwError "internal error: failed to generate equations for `{.ofConstName declName}`"
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
