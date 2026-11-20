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

This type checker adds the declaration `x := v` when it enters `let x := v; b`, but it keeps `b` in
bound-variable form. Every other binder gets a declaration in the same way. A subterm of `b` is put
into free-variable form only when the checker infers its type or compares it with `isDefEq`. Thus
entering a binder does not traverse its body, and the time is near-linear in the depth of nested
binders.

The checker checks a subterm only if the check can unfold a dependent `let`. In
`let x := 1; fun y : Nat => f y`, the type `Nat` of `y` cannot reach `x`, so the check of `f y` is
skipped. In `let x := 1; fun y : Fin x => f y`, the type of `y` can reach `x`, so the checker
checks `f y`.

A metavariable `?m` is created outside the `let`s that we visit, so its local context contains none
of their variables. Only a delayed assignment `?m #[x₁, …, xₙ] := ?p` can depend on such a `let`
variable `y`, when `y` reaches the argument for some `let` variable `xᵢ` of `?p`. Such a `y` remains
a `let`.

The traversal is very close to the one of `Sym.letToHave`, which differs as follows:
- It requires a maximally shared input and keeps the result maximally shared.
- It keys its caches by pointer, and compares terms by pointer before it calls `isDefEq`.
- It keeps every dependent `let` that has a metavariable in its body. This module keeps such a
  `let` only if its variable reaches a delayed assignment, as described above.

The trace class `trace.Meta.letToHave` reports statistics.
-/

namespace Lean.Meta

namespace LetToHave

/-- Returns `true` if there are any `letE (nondep := false)` subexpressions. -/
private def hasDepLet (e : Expr) : Bool :=
  Option.isSome <| e.find? (· matches .letE (nondep := false) ..)

private structure Context where
  /-- The number of dependent `let`s in scope. -/
  numCandidates : Nat := 0
  /--
  The number of innermost binders that are not dependent `let`s and whose types cannot reach one.
  Checking a subterm whose loose bound variables all refer to these binders cannot unfold a
  dependent `let`.
  -/
  cleanSuffix : Nat := 0

private structure State where
  /-- The scratch free variables of the enclosing binders: bvar `i` is `xs[xs.size - i - 1]`. -/
  xs : Array Expr := #[]
  /-- Results of `visit` for terms with loose bound variables, in the current binder scope. -/
  visited : Std.HashMap ExprStructEq Expr := {}
  /-- Types, in free-variable form, of terms with loose bound variables, in the current binder scope. -/
  types : Std.HashMap ExprStructEq Expr := {}
  /-- Results of `substEnv` in the current binder scope. -/
  subst : Std.HashMap ExprStructEq Expr := {}
  /-- Results of `visit` for closed terms. -/
  visitedClosed : Std.HashMap ExprStructEq Expr := {}
  /-- Results of `hasDepLetM`. -/
  hasDepLetCache : Std.HashMap ExprStructEq Bool := {}
  /-- The number of transformed `let` expressions. -/
  count : Nat := 0

private abbrev M := ReaderT Context (StateRefT State MetaM)

/-- Runs `x` with empty caches for the binder scope, and restores the current ones afterwards. -/
@[inline] private def withNewScope (x : M α) : M α := do
  let (visited, types, subst) ← modifyGet fun s =>
    ((s.visited, s.types, s.subst), { s with visited := {}, types := {}, subst := {} })
  try x finally
    modify fun s => { s with visited, types, subst }

/-- `hasDepLet` with a cache for every subterm. -/
private partial def hasDepLetM (e : Expr) : M Bool := do
  match e with
  | .letE (nondep := false) .. => return true
  | .letE _ t v b true => cached do hasDepLetM t <||> hasDepLetM v <||> hasDepLetM b
  | .app f a => cached do hasDepLetM f <||> hasDepLetM a
  | .lam _ t b _ | .forallE _ t b _ => cached do hasDepLetM t <||> hasDepLetM b
  | .mdata _ b | .proj _ _ b => cached do hasDepLetM b
  | _ => return false
where
  cached (k : M Bool) : M Bool := do
    if let some r := (← get).hasDepLetCache[(e : ExprStructEq)]? then
      return r
    let r ← k
    modify fun s => { s with hasDepLetCache := s.hasDepLetCache.insert e r }
    return r

/-- Puts `e` into free-variable form. -/
private def substEnv (e : Expr) : M Expr := do
  if !e.hasLooseBVars then
    return e
  if let some r := (← get).subst[(e : ExprStructEq)]? then
    return r
  let r := e.instantiateRev (← get).xs
  modify fun s => { s with subst := s.subst.insert e r }
  return r

/-- Checks `t =?= s`, where both terms are in free-variable form. -/
private def checkDefEq (t s : Expr) : M Unit := do
  unless (← isDefEq t s) do
    throwError "type mismatch{indentExpr t}\nis not definitionally equal to{indentExpr s}"

/-- Puts `type`, which is in free-variable form, into the form `.forallE ..`. -/
private def ensureForall (type : Expr) : M Expr := do
  if type.isForall then
    return type
  let type' ← whnf type
  unless type'.isForall do
    throwFunctionExpected type
  return type'

/-- Returns `true` if checking `e` cannot unfold a dependent `let` in scope. -/
@[inline] private def isClean (e : Expr) (ctx : Context) : Bool :=
  e.looseBVarRange ≤ ctx.cleanSuffix

/--
Given an expression `e` whose definition may be used in an unknown manner (for example, through a
metavariable), marks all `let` variables in `e` (or accessible through `e`) as unfolded.
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
Marks the `let` variables in scope on which the application `?m args` of a metavariable depends.
`args` are in free-variable form.
-/
private def checkMVar (mvarId : MVarId) (args : Array Expr) : M Unit := do
  let some { fvars, mvarIdPending } ← getDelayedMVarAssignment? mvarId | return
  unless fvars.size ≤ args.size do
    -- An invalid delayed assignment: every `let` in scope remains a `let`.
    for x in (← get).xs do
      if ← x.fvarId!.isLetVar then
        addZetaDeltaFVarId x.fvarId!
    return
  let pendingDecl ← mvarIdPending.getDecl
  for fvar in fvars, arg in args do
    if (pendingDecl.lctx.getFVar! fvar).isLet then
      visitDepExpr arg

mutual

/-- Transforms the `let`s of `e`, which is in bound-variable form, and checks `e`. -/
private partial def visit (e : Expr) : M Expr := do
  match e with
  | .bvar .. | .fvar .. | .sort .. | .const .. | .lit .. => return e
  | .mvar mvarId =>
    if (← read).numCandidates > 0 then checkMVar mvarId #[]
    return e
  | _ =>
    let ctx ← read
    if ctx.numCandidates == 0 || isClean e ctx then
      unless (← hasDepLetM e) do
        return e
    else if let .mvar mvarId := e.getAppFn then
      checkMVar mvarId (← e.getAppArgs.mapM substEnv)
    if !e.hasLooseBVars then
      visitClosed e
    else
      if let some r := (← get).visited[(e : ExprStructEq)]? then
        return r
      let r ← visitCore e
      modify fun s => { s with visited := s.visited.insert e r }
      return r

/-- Visits a closed term, whose result does not depend on the enclosing binders. -/
private partial def visitClosed (e : Expr) : M Expr := do
  if let some r := (← get).visitedClosed[(e : ExprStructEq)]? then
    return r
  let r ← withReader (fun _ => {}) do withNewScope do visitCore e
  modify fun s => { s with visitedClosed := s.visitedClosed.insert e r }
  return r

private partial def visitCore (e : Expr) : M Expr := do
  match e with
  | .app .. => visitApp e
  | .mdata _ b => return e.updateMData! (← visit b)
  | .proj _ _ b =>
    let r := e.updateProj! (← visit b)
    let ctx ← read
    if ctx.numCandidates > 0 && !isClean b ctx then
      discard <| inferTypeFallback e
    return r
  | .lam n t b _ =>
    let t' ← visit t
    let tf ← substEnv t'
    checkDomain t tf
    withBinder n tf none (tainted := !isClean t (← read)) (isCandidate := false) fun _ => do
      return e.updateLambdaE! t' (← visit b)
  | .forallE .. => visitForall e
  | .letE n t v b nondep =>
    let t' ← visit t
    let v' ← visit v
    let tf ← substEnv t'
    let ctx ← read
    if ctx.numCandidates > 0 then
      checkDomain t tf
      if !isClean t ctx || !isClean v ctx then
        if v.isLambda then
          checkFun v tf
        else
          checkDefEq (← inferTypeO v) tf
    let vf ← substEnv v'
    let isCandidate := !nondep
    -- The value of a `have` is hidden in the local context, so only a dependent `let` can leak
    -- its value.
    withBinder n tf (some (vf, nondep)) (tainted := isCandidate || !isClean t ctx) isCandidate fun x => do
      let b' ← visit b
      if nondep || (← getZetaDeltaFVarIds).contains x.fvarId! then
        return e.updateLetE! t' v' b'
      modify fun s => { s with count := s.count + 1 }
      return mkLet n t' v' b' (nondep := true)
  | _ => unreachable!

/--
Visits the application `e`. `visit` checks the metavariable head of `e` together with its arguments,
so this function does not visit that head on its own.
-/
private partial def visitApp (e : Expr) : M Expr := do
  let .app f a := e | unreachable!
  let f' ← if f.isApp then visitApp f else if f.isMVar then pure f else visit f
  let r := e.updateApp! f' (← visit a)
  if (← read).numCandidates > 0 then
    checkApp f a
  return r

/-- Visits a `∀`-telescope, and checks that its domains and its body are types. -/
private partial def visitForall (e : Expr) : M Expr := do
  match e with
  | .forallE n t b _ =>
    let t' ← visit t
    let tf ← substEnv t'
    checkDomain t tf
    withBinder n tf none (tainted := !isClean t (← read)) (isCandidate := false) fun _ => do
      return e.updateForallE! t' (← visitForall b)
  | _ =>
    let r ← visit e
    let ctx ← read
    if ctx.numCandidates > 0 && !isClean e ctx then
      discard <| getLevel (← substEnv r)
    return r

/-- Checks that the binder domain `t` is a type. `tf` is the free-variable form of `t`. -/
private partial def checkDomain (t tf : Expr) : M Unit := do
  let ctx ← read
  if ctx.numCandidates > 0 && !isClean t ctx then
    discard <| getLevel tf

/--
Adds a scratch declaration of type `type` (in free-variable form) to the local context, and runs `k`
on its free variable with empty caches for the binder scope. `value?` is the value and the `nondep`
flag of a `let`.
-/
private partial def withBinder (n : Name) (type : Expr) (value? : Option (Expr × Bool))
    (tainted : Bool) (isCandidate : Bool) (k : Expr → M α) : M α := do
  let fvarId ← mkFreshFVarId
  let x := mkFVar fvarId
  let lctx ← getLCtx
  let lctx := match value? with
    | some (v, nondep) => lctx.mkLetDecl fvarId n type v nondep
    | none => lctx.mkLocalDecl fvarId n type
  withLCtx lctx {} do
    withReader (fun ctx => { ctx with
        numCandidates := ctx.numCandidates + (if isCandidate then 1 else 0)
        cleanSuffix := if tainted then 0 else ctx.cleanSuffix + 1 }) do
      modify fun s => { s with xs := s.xs.push x }
      try withNewScope do k x
      finally modify fun s => { s with xs := s.xs.pop }

/-- Checks that the type of `a` is the domain of the type of `f`. -/
private partial def checkApp (f a : Expr) : M Unit := do
  let fnType ← ensureForall (← inferTypeO f)
  let .forallE _ d _ _ := fnType | unreachable!
  if !a.hasLooseBVars && !d.hasFVar then
    return ()
  if a.isLambda then
    checkFun a d
  else
    checkDefEq (← inferTypeO a) d

/--
Checks that the lambda `e` (in bound-variable form) has type `expected` (in free-variable form).
Compares the domains pairwise, and the type of the body with the codomain.
-/
private partial def checkFun (e : Expr) (expected : Expr) : M Unit := do
  match e with
  | .lam n t b _ =>
    let expected ← ensureForall expected
    let .forallE _ d body _ := expected | unreachable!
    let tf ← substEnv t
    checkDefEq tf d
    withBinder n tf none (tainted := !isClean t (← read)) (isCandidate := false) fun x => do
      checkFun b (body.instantiate1 x)
  | _ => checkDefEq (← inferTypeO e) expected

/-- The type of `e`, which is in bound-variable form. The type is in free-variable form. -/
private partial def inferTypeO (e : Expr) : M Expr := do
  if !e.hasLooseBVars then
    inferType e
  else
    if let some type := (← get).types[(e : ExprStructEq)]? then
      return type
    let type ← match e with
      | .bvar idx =>
        let xs := (← get).xs
        pure ((← getLCtx).getFVar! xs[xs.size - idx - 1]!).type
      | .mdata _ b => inferTypeO b
      | .app f a =>
        let fnType ← ensureForall (← inferTypeO f)
        let .forallE _ _ body _ := fnType | unreachable!
        if body.hasLooseBVars then
          pure (body.instantiate1 (← substEnv a))
        else
          pure body
      | _ => inferTypeFallback e
    modify fun s => { s with types := s.types.insert e type }
    return type

/-- Infers the type of a term with a binder or projection head. -/
private partial def inferTypeFallback (e : Expr) : M Expr := do
  let ef ← substEnv e
  -- A cache hit would not record the `let` variables that the inference unfolds.
  withTheReader Meta.Context (fun ctx => { ctx with cacheInferType := false }) do
    inferType ef

end

private def main (e : Expr) : MetaM Expr := do
  Prod.fst <$> withTraceNode `Meta.letToHave (fun
      | .ok (_, msg) => pure msg
      | .error ex => pure ex.toMessageData) do
    if hasDepLet e then
      withTrackingZetaDelta <|
      withTransparency TransparencyMode.all <|
      withInferTypeConfig do
        let (r, s) ← visit e |>.run {} |>.run {}
        if s.count == 0 then
          trace[Meta.letToHave] "result: (no change)"
        else
          trace[Meta.letToHave] "result:{indentExpr r}"
        return (r, m!"transformed {s.count} `let` expressions into `have` expressions")
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
