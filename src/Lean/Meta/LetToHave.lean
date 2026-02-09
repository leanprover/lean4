/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

prelude
public import Lean.Meta.Check
public import Lean.ReservedNameAction
public import Lean.AddDecl
public import Lean.Meta.Transform
public import Lean.Util.CollectFVars
public import Lean.Util.CollectMVars
import Init.Data.Range.Polymorphic.Iterators
import Init.While

public section

/-!
# Transforming nondependent `let`s into `have`s

A `let` expression `let x : t := v; b` is *nondependent* if `fun x : t => b` is type correct.
Nondependent `let`s are those that can be transformed into `have x := v; b`.
This module has a procedure that detects which `let`s are nondependent and does the transformation,
attempting to do so efficiently.

Dependence checking is approximated using the `withTrackingZetaDelta` technique:
given `let x := v; b`, we add a `x := v` declaration to the local context,
and then type check `b` with `withTrackingZetaDelta` enabled to record whether `x` is unfolded.
If `x` is not unfolded, then we know that `b` does not depend on `v`.
This is a conservative check, since `isDefEq` may unfold local definitions unnecessarily.

We do not use `Lean.Meta.check` directly. A naive algorithm would be to do `Meta.check (b.instantiate1 x)`
for each `let` body, which would involve rechecking subexpressions multiple times when there are nested `let`s,
and furthermore we do not need to fully typecheck the body when evaluating dependence.
Instead, we re-implement a type checking algorithm here to be able to interleave checking and transformation.

The trace class `trace.Meta.letToHave` reports statistics.

The transformation has very limited support for metavariables.
Any `let` that contains a metavariable remains a `let` for now.

Optimizations, present and future:
- We can avoid doing the transformation if the expression has no `let`s.
- We can also avoid doing the transformation to `let`-free subexpressions that are not inside a `let`,
  however checking for `let`s is O(n), so we only try this for expressions with a small `approxDepth`.
  (We can consider precomputing this somehow.)
  - The cache is currently responsible for the check.
  - We also do it before entering telescopes, to avoid unnecessary fvar overhead.
- If we are not currently inside a `let`, then we do not need to do full typechecking.
- We try to reuse Exprs to promote subexpression sharing.
- We might consider not transforming lets to haves if we are in a proof that is not inside a `let`.
  For now we assume `abstractNestedProofs` has already been applied.
-/

namespace Lean.Meta

namespace LetToHave

/--
Returns `true` if there are any `letE (nondep := false)` subexpressions.
If true, then we must be sure to visit the subexpression.
If false, then we might still need to visit the subexpression,
but if we are not currently under any nondependent lets it is safe to skip it.
-/
private def hasDepLet (e : Expr) : Bool :=
  Option.isSome <| e.find? (· matches .letE (nondep := false) ..)

/--
Heuristic for skipping subexpressions. If true, we definitely can skip.

The default max depth of `5` was not experimentally optimized, except to see that it was faster than `0`.
-/
private def canSkip (e : Expr) (maxDepth : UInt32 := 5) : Bool :=
  !e.hasFVar && !e.hasExprMVar && (e.approxDepth ≤ maxDepth && !hasDepLet e)

private structure Result where
  /-- The transformed expression. -/
  expr : Expr
  /-- The type of `expr`, if it has been computed. -/
  type? : Option Expr
  deriving Inhabited

private local instance : Coe Result Expr where coe := Result.expr

private structure Context where
  /-- The dependent lets we are currently under.
  If this list is nonempty, then full typechecking is necessary. -/
  letFVars : List FVarId := []

private structure State where
  /-- The number of transformed `let` expressions. See `incCount`. -/
  count : Nat := 0
  /-- Cached results for `visit`. -/
  results : Std.HashMap ExprStructEq Result := {}

private abbrev M := ReaderT Context (StateRefT State MetaM)

/-- Gives the type of `r.expr`. If it has not been computed yet, updates the cache. -/
private def Result.type (r : Result) : M Expr := do
  if let some type := r.type? then
    return type
  else
    let type ← inferType r.expr
    let r := { r with type? := type }
    modify fun s => { s with results := s.results.insert r.expr r }
    return type

/-- Returns `true` if we need to do full typechecking due to `let` variables being in scope. -/
private def Context.check (ctx : Context) : Bool := !ctx.letFVars.isEmpty

/-- If we don't need full typechecking, returns `e`, otherwise evaluates `m`. -/
private def whenCheck (e : Expr) (m : M Result) : M Result := do
  if (← read).check then m else return { expr := e, type? := none }

/-- Executes `m` in a context where `letFVars := fvars`. -/
private def withLetFVars (fvars : List FVarId) (m : M α) : M α := do
  withReader (fun ctx => { ctx with letFVars := fvars }) m

/-- Increments the count of the number of `let`s transformed into `have`s. -/
private def incCount : M Unit :=
  modify fun s => { s with count := s.count + 1 }

/--
Finds a pre-existing result in the cache.
Note that the result might have no type, which happens for example if it was visited when `check` is false.
-/
private def findCache? (e : Expr) : M (Option Result) := do
  return (← get).results[(e : ExprStructEq)]?

/--
Finds `e` in the cache, or otherwise computes `m`.

If not in the cache, applies a cheap check to see if we can skip descending into the expression.
-/
private def checkCache (e : Expr) (m : M Result) : M Result := do
  if let some r ← findCache? e then
    return r
  else
    -- `2` was not experimentally optimized
    let r ← if canSkip (maxDepth := 2) e then
      pure { expr := e, type? := none }
    else
      m
    modify fun st => { st with results := st.results.insert e r }
    return r

/-- Like `findMCache?` but checks that `e` doesn't have any loose bvars. -/
private def findCacheNoBVars? (e : Expr) : M (Option Result) :=
  if e.hasLooseBVars then pure none else findCache? e

private def visitFVar (e : Expr) : MetaM Result := do
  let some decl ← e.fvarId!.findDecl? | e.fvarId!.throwUnknown
  return { expr := e, type? := decl.type }

/--
Give an expression `e` whose definition may be used in an unknown manner (for example, through a metavariable),
marks all fvars in `e` (or accessible through `e`) that can potentially be unfolded.

Assumption: while there may be metavariables in `e` (or in types of fvars present in `e`),
they have already been processed by `checkMVar` or will be processed by it.
-/
private def visitDepExpr (e : Expr) : M Unit := do
  let mut visited : FVarIdSet := {}
  let mut worklist := #[e]
  while !worklist.isEmpty do
    let e ← instantiateMVars worklist.back!
    worklist := worklist.pop
    for fvarId in (collectFVars {} e).fvarIds do
      unless visited.contains fvarId do
        visited := visited.insert fvarId
        if ← fvarId.isLetVar then
          addZetaDeltaFVarId fvarId
        worklist := worklist.push (← fvarId.getType)

/--
Checks whether the mvar creates a dependency on any let fvars.
Note: the local context of `mvarId` cannot depend on `letFVars`, since it was created outside these `let`s.
The only consideration is delayed assignments and which variables they depend on;
if the fvar is not passed among the `args`, the mvar cannot depend on it.
-/
private def checkMVar (mvarId : MVarId) (args : Array Expr) : M Unit := do
  if let some { fvars, mvarIdPending } ← getDelayedMVarAssignment? mvarId then
    let letFVars := (← read).letFVars
    unless fvars.size ≤ args.size do
      -- This is an invalid delayed assignment. Mark all `letFVars` to inhibit transformation.
      letFVars.forM (addZetaDeltaFVarId ·)
      return
    let pendingDecl ← mvarIdPending.getDecl
    for fvar in fvars, arg in args do
      let fvarDecl := pendingDecl.lctx.getFVar! fvar
      if fvarDecl.isLet then
        visitDepExpr arg

private def visitMVar (e : Expr) : M Result := do
  let some decl ← e.mvarId!.findDecl? | throwUnknownMVar e.mvarId!
  if (← read).check then checkMVar e.mvarId! #[]
  return { expr := e, type? := decl.type }

private def visitConst (e : Expr) : M Result := do
  whenCheck e do
    let .const constName us := e | unreachable!
    let cinfo ← getConstVal constName
    if cinfo.levelParams.length == us.length then
      let type ← instantiateTypeLevelParams cinfo us
      return { expr := e, type? := type }
    else
      throwIncorrectNumberOfLevels constName us

/--
When checking, makes sure that `r.type?` is of the form `Expr.sort _`.
-/
private def ensureType (r : Result) : M Result := do
  if (← read).check then
    let type ← r.type
    let r := { r with type? := type }
    if type.isSort then
      return r
    else
      let .sort u ← whnf type | throwTypeExpected r
      let r := { r with type? := Expr.sort u }
      modify fun s => { s with results := s.results.insert r.expr r }
      return r
  else
    return r

/--
Note: We want to cache all prefixes of each application, hence no `instantiateRevRange`-type logic here.
-/
private def visitApp (e : Expr) (f a : Result) : M Result := do
  if (← read).check then
    let mut fType ← f.type
    unless fType.isForall do
      fType ← whnf fType
    match fType with
    | Expr.forallE _ d b _ =>
      unless (← isDefEq d (← a.type)) do
        throwAppTypeMismatch f a
      return { expr := e.updateApp! f a, type? := b.instantiate1 a }
    | _ => throwFunctionExpected (mkApp f a)
  else
    return { expr := e.updateApp! f a, type? := none }

mutual

private partial def visitType (e : Expr) : M Result := do
  let r ← visit e
  ensureType r

private partial def visitAppArgs (e : Expr) : M Result := do
  if (← read).check then
    if let .mvar mvarId := e.getAppFn then
      checkMVar mvarId e.getAppArgs
    let rec go (e : Expr) : M Result := do
      let Expr.app f a := e | visit e
      visitApp e (← checkCache f <| go f) (← visit a)
    go e
  else
    -- If not checking, skip caching each prefix.
    let rec go' (e : Expr) : M Expr := do
      let Expr.app f a := e | visit e
      return e.updateApp! (← go' f) (← visit a)
    return { expr := ← go' e, type? := none }

private partial def visitForall (e : Expr) : M Result := do
  if canSkip e then
    return { expr := e, type? := none }
  else
    go (← getLCtx) #[] #[] e
where
  go (lctx : LocalContext) (fvars : Array Expr) (doms : Array Result) (e : Expr) : M Result := do
    if let some e' ← findCacheNoBVars? e then
      return ← withLCtx lctx {} do finalize fvars doms e'
    else
      match e with
      | .forallE n t b bi =>
        let t ← withLCtx lctx {} do visitType (t.instantiateRev fvars)
        let fvarId ← mkFreshFVarId
        let lctx := lctx.mkLocalDecl fvarId n t.expr bi
        go lctx (fvars.push (.fvar fvarId)) (doms.push t) b
      | _ =>
        withLCtx lctx {} do
          let e' ← visit (e.instantiateRev fvars)
          finalize fvars doms e'
  finalize (fvars : Array Expr) (doms : Array Result) (body : Result) : M Result := do
    let e' := (← getLCtx).mkForall fvars body
    if (← read).check then
      let bodyLevel := (← ensureType body).type?.get!.sortLevel!
      let u ← doms.foldrM (init := bodyLevel) fun dom u =>
        return mkLevelIMax' (← dom.type).sortLevel! u
      return { expr := e', type? := Expr.sort u }
    else
      return { expr := e', type? := none }

/--
Visits lambdas, lets, and haves.

Enters the entire telescope at once.
We do not check the cache at each step of the telescope since we assume that there are no unused variables.
-/
private partial def visitLambdaLet (e : Expr) : M Result := do
  if canSkip e then
    return { expr := e, type? := none }
  else
    go (← getLCtx) #[] e (← read).letFVars
where
  /--
  Enters a lambda/let/have telescope, checking that each domain type is a type.
  For let/have, checks that each value has a type defeq to the domain type.
  Calls `finalize` once the telescope is constructed.
  -/
  go (lctx : LocalContext) (fvars : Array Expr) (e : Expr) (letFVars : List FVarId) : M Result := do
    let inCtx (v : Expr → M Result) (e : Expr) : M Result :=
      withLCtx lctx {} <| withLetFVars letFVars <| v (e.instantiateRev fvars)
    match e with
    | .lam n t b bi =>
      let t ← inCtx visitType t
      let fvarId ← mkFreshFVarId
      let lctx  := lctx.mkLocalDecl fvarId n t.expr bi
      go lctx (fvars.push (.fvar fvarId)) b letFVars
    | .letE n t v b nondep =>
      let t ← inCtx visitType t
      let v ← inCtx visit v
      unless letFVars.isEmpty do withLCtx' lctx do
        let vType ← v.type
        unless (← isDefEq t vType) do
          throwError "invalid let declaration, term{indentExpr v}{← mkHasTypeButIsExpectedMsg vType t}"
      let fvarId ← mkFreshFVarId
      let lctx  := lctx.mkLetDecl fvarId n t v nondep
      let letFVars := if nondep then letFVars else fvarId :: letFVars
      go lctx (fvars.push (.fvar fvarId)) b letFVars
    | _ =>
      inCtx (finalize fvars <=< visit) e
  /--
  This function rebuilds the expression and converts `let`s to `have`s when possible.
  -/
  finalize (fvars : Array Expr) (body : Result) : M Result := do
    trace[Meta.letToHave.debug] "finalize {fvars},{indentD m!"{body.expr} : {body.type?}"}"
    let body' := {
      expr := body.expr.abstract fvars
      type? := body.type?.map (·.abstract fvars)
    }
    Nat.foldRevM fvars.size (init := body') fun i _ res => do
      let .fvar fvarId := fvars[i] | unreachable!
      let some decl ← fvarId.findDecl? | fvarId.throwUnknown
      match decl with
      | .cdecl _ _ n t bi _ => do
        let t := t.abstractRange i fvars
        pure {
          expr := Expr.lam n t res.expr bi
          type? := res.type?.map fun type => Expr.forallE n t type bi
        }
      | .ldecl _ _ n t v nondep _ => do
        let nondep ←
          if nondep then pure true
          else if !(← getZetaDeltaFVarIds).contains fvarId then incCount; pure true
          else pure false
        let t := t.abstractRange i fvars
        let v := v.abstractRange i fvars
        pure {
          expr := Expr.letE n t v res.expr nondep
          type? := res.type?.map fun type =>
            if type.hasLooseBVar 0 then
              Expr.letE n t v type nondep
            else
              type.lowerLooseBVars 1 1
        }

private partial def visitProj (e : Expr) (structName : Name) (idx : Nat) (struct : Result) : M Result := do
  unless (← read).check do
    return { expr := e.updateProj! struct, type? := none }
  let structType ← whnf (← struct.type)
  let prop ← isProp structType
  let failed {α} (_ : Unit) : M α := throwError "invalid projection{indentExpr (mkProj structName idx struct)}\nfrom type{indentExpr structType}"
  matchConstStructure structType.getAppFn failed fun structVal structLvls ctorVal => do
    unless structVal.name == structName do failed ()
    let structTypeArgs := structType.getAppArgs
    if structVal.numParams + structVal.numIndices != structTypeArgs.size then
      failed ()
    let mut ctorType ← inferType <| mkAppN (mkConst ctorVal.name structLvls) structTypeArgs[*...structVal.numParams]
    let mut args := #[]
    let mut j := 0
    let mut lastFieldTy : Expr := default
    for i in *...=idx do
      unless ctorType.isForall do
        ctorType ← whnf <| ctorType.instantiateRevRange j i args
        j := i
      let .forallE _ dom body _ := ctorType | failed ()
      let dom := dom.instantiateRevRange j i args
      if prop then unless ← isProp dom do failed ()
      args := args.push <| Expr.proj structName i struct
      ctorType := body
      lastFieldTy := dom
    lastFieldTy := lastFieldTy.cleanupAnnotations
    return { expr := e.updateProj! struct, type? := lastFieldTy }

private partial def visit (e : Expr) : M Result := do
  withTraceNode `Meta.letToHave.debug (fun res =>
      return m!"{if res.isOk then checkEmoji else crossEmoji} visit (check := {(← read).check}){indentExpr e}") do
    match e with
    | .bvar .. => throwError "unexpected bound variable {e}"
    | .fvar .. => visitFVar e
    | .mvar .. => visitMVar e
    | .sort u => return { expr := e, type? := Expr.sort u.succ }
    | .const .. => visitConst e
    | .app .. => checkCache e do visitAppArgs e
    | .forallE .. => checkCache e do visitForall e
    | .lam .. | .letE .. => checkCache e do visitLambdaLet e
    | .lit v => return { expr := e, type? := v.type }
    | .mdata _ e' => let e' ← visit e'; return { e' with expr := e.updateMData! e' }
    | .proj structName idx struct => checkCache e do visitProj e structName idx (← visit struct)

end

private def main (e : Expr) : MetaM Expr := do
  Prod.fst <$> withTraceNode `Meta.letToHave (fun
      | .ok (_, msg) => pure m!"{checkEmoji} {msg}"
      | .error ex => pure m!"{crossEmoji} {ex.toMessageData}") do
    if hasDepLet e then
      withTrackingZetaDelta <|
      withTransparency TransparencyMode.all <|
      withInferTypeConfig do
        let (r, s) ← visit e |>.run {} |>.run {}
        if s.count == 0 then
          trace[Meta.letToHave] "result: (no change)"
        else
          trace[Meta.letToHave] "result:{indentExpr r.expr}"
        return (r.expr, m!"transformed {s.count} `let` expressions into `have` expressions")
    else
      return (e, "no `let` expressions")

end LetToHave

/--
Transforms nondependent `let` expressions into `have` expressions.
If `e` is not type correct, returns `e`.
The `Meta.letToHave` trace class logs errors and messages.
-/
def letToHave (e : Expr) : MetaM Expr := do
  profileitM Exception "let-to-have transformation" (← getOptions) do
    let e ← instantiateMVars e
    withoutExporting <| LetToHave.main e

builtin_initialize
  registerTraceClass `Meta.letToHave
  registerTraceClass `Meta.letToHave.debug

end Lean.Meta
