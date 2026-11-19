/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.SymM
import Lean.Meta.Sym.InferType
import Lean.Meta.Sym.ReplaceS
import Lean.Meta.Sym.AlphaShareBuilder
namespace Lean.Meta.Sym
open Lean.Meta.Sym.Internal

/-!
# `let`-to-`have` for `SymM`

`Sym.letToHave` converts nondependent `let` declarations of a term into `have`
declarations (i.e., sets the `nondep` flag of `.letE` nodes). The result is
definitionally equal to the input, has exactly the same shape, and preserves maximal
sharing: only the nodes on the path from the root to each converted `let` are rebuilt.

A `let x := v; b` is nondependent if `b` typechecks with `x` opaque. As in
`Meta.letToHave`, this is decided with the `withTrackingZetaDelta` technique: the body is
checked with `x` declared as a zeta-expandable declaration, and `x` is nondependent iff
no check needed to unfold it. Unlike `Meta.letToHave`, the traversal:

- keeps bodies in bound-variable form — no `instantiate`/`abstract` round-trip per
  binder, which makes the traversal near-linear on nested binders with open bodies
  (`Meta.letToHave` is quadratic there);
- discharges checking obligations only on subterms that can reach a candidate `let`:
  subterms without loose bound variables, and subterms whose loose bound variables all
  refer to "clean" binders, are skipped in O(1);
- discharges each obligation via pointer equality (the usual case in the maximally
  shared world), falling back to the tracked `Meta.isDefEq`.

`instantiate` is used in exactly two places: to put a binder's type (and value, for a
`let`) into free-variable form before adding the scratch declaration to the local
context, and to put terms into free-variable form before `inferType`/`isDefEq` calls.

Caching follows the two-tier discipline of `Sym.liftLets`: results and inferred types
for terms with loose bound variables are cached per binder scope (the scoped caches are
saved and reset when entering a binder body, and restored on exit — entries computed at
an outer binder offset must be invisible inside), while results for closed terms are
context-free and cached for the whole run; closed-term types go through the session
`Sym.inferType` cache.

Metavariables are opaque for the analysis (the whole run is under `withNewMCtxDepth`,
so pre-existing metavariables are rigid for `isDefEq` and can never be assigned by an
obligation), but a dependent `let` whose subtree contains one is conservatively kept:
a future assignment could depend on the `let` variable's value. Metavariables outside
a `let`'s subtree do not inhibit its conversion.
-/

namespace LetToHave

structure Context where
  /-- FVars for the enclosing binders: bvar `i` maps to `xs[xs.size - i - 1]`. -/
  xs : PArray Expr := {}
  /-- Number of candidate `let` declarations in scope. Obligations are discharged iff > 0. -/
  numCandidates : Nat := 0
  /--
  Number of consecutive clean innermost binders. A binder is clean if it is not a
  candidate and its type cannot reach a candidate. A subterm `e` with
  `e.looseBVarRange ≤ cleanSuffix` only references clean binders, so type checking it
  cannot unfold any candidate, and it can be skipped (given it has no `let` to convert).
  -/
  cleanSuffix : Nat := 0

structure State where
  /-- Scoped: transformation results for terms with loose bvars, per binder scope. -/
  visited : Std.HashMap ExprPtr Expr := {}
  /-- Scoped: types (in fvar form) for terms with loose bvars, per binder scope. -/
  types : Std.HashMap ExprPtr Expr := {}
  /-- Scoped: `substEnv` results, per binder scope. -/
  subst : Std.HashMap ExprPtr Expr := {}
  /-- Per-run: transformation results for closed terms. -/
  visitedClosed : Std.HashMap ExprPtr Expr := {}
  /-- Per-run: pointer-cached "contains a dependent `let`". -/
  hasDepLetCache : Std.HashMap ExprPtr Bool := {}
  /-- Number of converted `let` declarations. -/
  numConverted : Nat := 0

abbrev M := ReaderT Context (StateRefT State SymM)

/--
Runs `x` with fresh scoped caches, restoring the current ones afterwards. Used when
entering a binder body: entries computed at the outer binder offset denote different
terms inside and must be invisible there.
-/
@[inline] def withNewScope (x : M α) : M α := do
  let (visited, types, subst) ← modifyGet fun s =>
    ((s.visited, s.types, s.subst), { s with visited := {}, types := {}, subst := {} })
  try x finally
    modify fun s => { s with visited, types, subst }

/-- Returns `true` if `e` contains a `.letE` with `nondep := false`. Pointer-cached per run. -/
partial def hasDepLet (e : Expr) : M Bool := do
  match e with
  | .letE (nondep := false) .. => return true
  | .letE _ t v b true => cached e do hasDepLet t <||> hasDepLet v <||> hasDepLet b
  | .app f a => cached e do hasDepLet f <||> hasDepLet a
  | .lam _ t b _ | .forallE _ t b _ => cached e do hasDepLet t <||> hasDepLet b
  | .mdata _ b | .proj _ _ b => cached e do hasDepLet b
  | _ => return false
where
  cached (e : Expr) (k : M Bool) : M Bool := do
    if let some r := (← get).hasDepLetCache[{ expr := e : ExprPtr }]? then
      return r
    let r ← k
    modify fun s => { s with hasDepLetCache := s.hasDepLetCache.insert { expr := e } r }
    return r

/--
Substitutes the loose bound variables of `e` with the corresponding scratch fvars,
producing a term in free-variable form. The result is maximally shared.

Not `instantiateRevS`: the environment is a `PArray` (pushing per binder while enclosing
frames hold their versions would make an `Array` copy on every push), and results are
cached per binder scope, so repeated substitutions of a subterm across obligations in
the same scope are one lookup. Same design as `LiftLet.substEnv`.
-/
def substEnv (e : Expr) : M Expr := do
  if !e.hasLooseBVars then
    return e
  if let some r := (← get).subst[{ expr := e : ExprPtr }]? then
    return r
  let xs := (← read).xs
  let n := xs.size
  let r ← replaceS e fun sub offset => do
    match sub with
    | .bvar idx =>
      if idx ≥ offset then
        pure (some xs[n - (idx - offset) - 1]!)
      else
        pure (some sub)
    | .lit _ | .mvar _ | .fvar _ | .const _ _ | .sort _ => pure (some sub)
    | _ => if offset ≥ sub.looseBVarRange then pure (some sub) else pure none
  modify fun s => { s with subst := s.subst.insert { expr := e } r }
  return r

/--
Discharges the defeq obligation `t ≡ s` (both in fvar form): pointer equality, then the
tracked `Meta.isDefEq`. The input term is type correct, so `isDefEq` succeeds and
records which candidates had to be unfolded.
-/
def checkDefEq (t s : Expr) : M Unit := do
  if isSameExpr t s then
    return ()
  unless (← Meta.isDefEq t s) do
    throwError "`Sym.letToHave` failed, type error{indentExpr t}\nis not definitionally equal to{indentExpr s}"

/-- Ensures `type` (in fvar form) is a `.forallE`, using tracked `whnf` if needed. -/
def ensureForall (type : Expr) : M Expr := do
  if type.isForall then
    return type
  let type ← whnf type
  unless type.isForall do
    throwError "`Sym.letToHave` failed, function expected{indentExpr type}"
  shareCommon type

/--
Returns `true` if type checking `e` cannot create an obligation that reaches a
candidate: `e` is closed, or all its loose bound variables refer to clean binders.
-/
@[inline] def isClean (e : Expr) (ctx : Context) : Bool :=
  e.looseBVarRange ≤ ctx.cleanSuffix

mutual

/--
Main traversal: converts the `let`s of `e` and discharges the checking obligations of
the enclosing candidates. `e` is in bound-variable form w.r.t. the enclosing binders.
-/
partial def visit (e : Expr) : M Expr := do
  match e with
  | .bvar .. | .fvar .. | .mvar .. | .sort .. | .const .. | .lit .. => return e
  | _ =>
    let ctx ← read
    if ctx.numCandidates == 0 || isClean e ctx then
      -- No obligation can arise from this subterm; visit only if there is a `let` to convert.
      unless (← hasDepLet e) do
        return e
    if !e.hasLooseBVars then
      visitClosed e
    else
      if let some r := (← get).visited[{ expr := e : ExprPtr }]? then
        return r
      let r ← visitCore e
      modify fun s => { s with visited := s.visited.insert { expr := e } r }
      return r

/--
Visits a closed term. The result does not depend on the environment: obligations inside
cannot reach any enclosing candidate, and its own candidates are self-contained. Cached
for the whole run.
-/
partial def visitClosed (e : Expr) : M Expr := do
  if let some r := (← get).visitedClosed[{ expr := e : ExprPtr }]? then
    return r
  let r ← withReader (fun _ => { xs := {}, numCandidates := 0, cleanSuffix := 0 }) do
    withNewScope do visitCore e
  modify fun s => { s with visitedClosed := s.visitedClosed.insert { expr := e } r }
  return r

partial def visitCore (e : Expr) : M Expr := do
  match e with
  | .app f a =>
    let r ← e.updateAppS! (← visit f) (← visit a)
    if (← read).numCandidates > 0 then
      checkApp f a
    return r
  | .mdata _ b => e.updateMDataS! (← visit b)
  | .proj _ _ b =>
    let r ← e.updateProjS! (← visit b)
    let ctx ← read
    if ctx.numCandidates > 0 && !isClean b ctx then
      -- The struct type may need tracked `whnf` to expose the structure.
      discard <| inferTypeFallback e
    return r
  | .lam n t b _ =>
    let t' ← visit t
    let tf ← substEnv t'
    checkDomain t tf
    withBinder n tf none (tainted := !isClean t (← read)) (isCandidate := false) fun _ => do
      e.updateLambdaS! t' (← visit b)
  | .forallE .. => visitForall e
  | .letE n t v b nondep =>
    let t' ← visit t
    let v' ← visit v
    let tf ← substEnv t'
    let ctx ← read
    if ctx.numCandidates > 0 then
      checkDomain t tf
      if !isClean t ctx || !isClean v ctx then
        -- The value's type must match the annotation without unfolding candidates.
        if v.isLambda then
          checkFun v tf
        else
          checkDefEq (← inferTypeO v) tf
    let vf ← substEnv v'
    -- Conservative: a dependent `let` whose subtree contains a metavariable is not a
    -- candidate — a future assignment could depend on its value (cf. `Meta.letToHave`,
    -- which keeps such `let`s based on the metavariable's local context; that
    -- information is not available in bound-variable form). It is still added as a
    -- zeta-expandable declaration and treated as tainted: its value can leak enclosing
    -- candidates during checks.
    let isDep := !nondep
    let isCandidate := isDep && !e.hasExprMVar
    withBinder n tf (some (vf, nondep)) (tainted := isDep || !isClean t ctx) isCandidate fun x => do
      let b' ← visit b
      let nondep' ←
        if nondep then pure true
        else if !isCandidate then pure false
        else if (← getZetaDeltaFVarIds).contains x.fvarId! then pure false
        else do
          modify fun s => { s with numConverted := s.numConverted + 1 }
          pure true
      if nondep' == nondep then
        e.updateLetS! t' v' b'
      else
        mkLetS n t' v' b' nondep'
  | _ => unreachable!

/--
Visits a `∀`-telescope. Sort obligations: one tracked `getLevel` per non-clean domain,
and one for the terminal body. Processing the chain in one pass keeps the terminal-body
obligation linear in the telescope length.
-/
partial def visitForall (e : Expr) : M Expr := do
  match e with
  | .forallE n t b _ =>
    let t' ← visit t
    let tf ← substEnv t'
    checkDomain t tf
    withBinder n tf none (tainted := !isClean t (← read)) (isCandidate := false) fun _ => do
      e.updateForallS! t' (← visitForall b)
  | _ =>
    let r ← visit e
    let ctx ← read
    if ctx.numCandidates > 0 && !isClean e ctx then
      discard <| Meta.getLevel (← substEnv r)
    return r

/--
Sort obligation for a binder domain: `tf` (the domain in fvar form) must be a type.
Skipped when the domain cannot reach a candidate.
-/
partial def checkDomain (t tf : Expr) : M Unit := do
  let ctx ← read
  if ctx.numCandidates > 0 && !isClean t ctx then
    discard <| Meta.getLevel tf

/--
Adds the scratch declaration for a binder, installs the extended local context, and runs
`k` with the extended environment and fresh scoped caches, so every `Meta` operation in
the binder scope sees the scratch declarations. `value?` provides the (fvar-form) value
and `nondep` flag for `let`/`have` binders.
-/
partial def withBinder (n : Name) (type : Expr) (value? : Option (Expr × Bool))
    (tainted : Bool) (isCandidate : Bool) (k : Expr → M α) : M α := do
  let fvarId ← mkFreshFVarId
  let x ← mkFVarS fvarId
  let lctx ← getLCtx
  let lctx := match value? with
    | some (v, nondep) => lctx.mkLetDecl fvarId n type v nondep
    | none => lctx.mkLocalDecl fvarId n type
  withLCtx lctx {} do
    withReader (fun ctx => { ctx with
        xs := ctx.xs.push x
        numCandidates := ctx.numCandidates + (if isCandidate then 1 else 0)
        cleanSuffix := if tainted then 0 else ctx.cleanSuffix + 1 }) do
      withNewScope do k x

/--
Obligation for the application node `f a`: the type of `a` must match the domain of the
type of `f` without unfolding candidates. When `a` is a lambda, the comparison is
decomposed binder-wise (`checkFun`) so that the lambda's type is never materialized.
-/
partial def checkApp (f a : Expr) : M Unit := do
  let fnType ← ensureForall (← inferTypeO f)
  let .forallE _ d _ _ := fnType | unreachable!
  if !a.hasLooseBVars && !d.hasFVar then
    -- Neither side can reach a candidate.
    return ()
  if a.isLambda then
    checkFun a d
  else
    checkDefEq (← inferTypeO a) d

/--
Checks that the lambda `e` (in bvar form) has type `expected` (in fvar form) without
materializing the lambda's type: domains are compared pairwise, and at the leaf the
body's type is compared with the codomain.
-/
partial def checkFun (e : Expr) (expected : Expr) : M Unit := do
  match e with
  | .lam n t b _ =>
    let expected ← ensureForall expected
    let .forallE _ d body _ := expected | unreachable!
    let tf ← substEnv t
    checkDefEq tf d
    withBinder n tf none (tainted := !isClean t (← read)) (isCandidate := false) fun x => do
      let body ← if body.hasLooseBVars then share (body.instantiate1 x) else pure body
      checkFun b body
  | _ => checkDefEq (← inferTypeO e) expected

/--
Returns the type (in fvar form, maximally shared) of `e` (in bvar form). Pure
inference: obligations are discharged by `visit`, not here. Closed terms go through the
session `Sym.inferType` cache; open terms are cached per binder scope.
-/
partial def inferTypeO (e : Expr) : M Expr := do
  if !e.hasLooseBVars then
    Sym.inferType e
  else
    if let some type := (← get).types[{ expr := e : ExprPtr }]? then
      return type
    let type ← match e with
      | .bvar idx =>
        let xs := (← read).xs
        let x := xs[xs.size - idx - 1]!
        pure ((← getLCtx).getFVar! x).type
      | .mdata _ b => inferTypeO b
      | .app f a =>
        let fnType ← ensureForall (← inferTypeO f)
        let .forallE _ _ body _ := fnType | unreachable!
        if body.hasLooseBVars then
          share (body.instantiate1 (← substEnv a))
        else
          pure body
      | _ => inferTypeFallback e
    modify fun s => { s with types := s.types.insert { expr := e } type }
    return type

/--
Fallback type inference for open terms with binder or projection heads: substitutes the
scratch fvars and calls `Meta.inferType` (tracked, without the `MetaM` infer-type cache).
-/
partial def inferTypeFallback (e : Expr) : M Expr := do
  let ef ← substEnv e
  let type ← withTheReader Meta.Context (fun ctx => { ctx with cacheInferType := false }) do
    Meta.inferType ef
  -- Not needed for correctness: it keeps the invariant that all cached types are
  -- maximally shared, so `checkDefEq`'s pointer-equality fast path can fire on them.
  shareCommon type

end

end LetToHave

open LetToHave in
/--
Converts the nondependent `let` declarations of `e` into `have` declarations. The
result is definitionally equal to `e`, has the same shape (only `nondep` flags change),
and is maximally shared. If nothing is converted, the result is pointer-equal to `e`
(check with `isSameExpr`).

Assumptions: `e` is maximally shared, has no loose bound variables, and is type
correct. Metavariables are treated as opaque values.
-/
public def letToHave (e : Expr) : SymM Expr := do
  if e.hasLooseBVars then
    throwError "`Sym.letToHave` internal error, input term has loose bound variables"
  -- The `withConfig` step is the (monad-generic) equivalent of `withInferTypeConfig`.
  -- `withNewMCtxDepth` makes pre-existing metavariables rigid: obligations cannot assign them.
  withoutExporting <| withNewMCtxDepth <| withTrackingZetaDelta <| withTransparency TransparencyMode.all <|
    withConfig (fun cfg => { cfg with
      beta := true, iota := true, zeta := true, zetaHave := true, zetaDelta := true
      proj := .yesWithDelta, etaStruct := .all }) do
    withLCtx (← getLCtx) {} do
      let x : M Expr := do
        if (← hasDepLet e) then visit e else return e
      x.run {} |>.run' {}

end Lean.Meta.Sym
