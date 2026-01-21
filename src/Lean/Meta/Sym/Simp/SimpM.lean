/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.SymM
public import Lean.Meta.Sym.Pattern
public section
namespace Lean.Meta.Sym.Simp

/-!
# Structural Simplifier for Symbolic Simulation

It is a specialized simplifier designed for symbolic simulation workloads.
It addresses performance bottlenecks identified in the standard `simp` tactic
when applied to large terms typical in symbolic execution.

## Design Goals

1. **Efficient caching** via pointer-based keys on maximally shared terms
2. **Fast pattern matching** using the `Pattern` infrastructure instead of `isDefEq`
3. **Minimal proof term overhead** by using `shareCommon` and efficient congruence lemma application

## Key Performance Problems Addressed

### 1. Cache Inefficiency (Hash Collisions)

The standard simplifier uses structural equality for cache keys. With large terms,
hash collisions cause O(n) comparisons that fail, leading to O(n²) behavior.

**Solution:** Require maximally shared input terms (`shareCommon`) and use
pointer-based cache keys. Structurally equal terms have equal pointers, making
cache lookup O(1).

### 2. `isDefEq` in Rewrite Matching

Profiling shows that `isDefEq` dominates simplification time in many workloads.
For each candidate rewrite rule, definitional equality checking with metavariable unification
is performed, and sometimes substantial time is spent checking whether the scopes are
compatible.

**Solution:** Use the `Pattern` infrastructure for syntactic matching:
- No metavariable creation or assignment
- No occurs check (`CheckAssignment`)
- Direct de Bruijn index comparison

### 3. `inferType` in Proof Construction

In the standard simplifier, building `Eq.trans` and `congrArg` proofs uses `inferType` on proof terms,
which reconstructs large expressions and destroys sharing. It often causes O(n²) allocation.

**Solution:**
- Never perform `inferType` on proof terms when constructing congruence and transitivity proofs.
- Use a pointer-based cache for `inferType` on terms.

### 4. `funext` Proof Explosion

Nested `funext` applications create O(n²) proof terms due to implicit arguments
`{f} {g}` of size O(n) repeated n times.

**Solution:** Generate `funext_k` for k binders at once, stating the implicit
arguments only once.

### 5. Binder Re-entry Cache Invalidation

When a simplification theorem restructures a lambda, re-entering creates a fresh
free variable, invalidating all cached results for subterms.

**Solution:** Reuse free variables across binder re-entry when safe:
- Stack-based approach: reuse when types match on re-entry path
- Instance-aware: track local type class instances separately from hypotheses
- If simplifier doesn't discharge hypotheses from local context, only instances matter

### 6. Contextual `ite` Handling

The standard `ite_congr` theorem adds hypotheses when entering branches,
invalidating the cache and causing O(2^n) behavior on conditional trees.

**Solution:** Non-contextual `ite` handling for symbolic simulation:
- Only simplify the condition
- If condition reduces to `True`/`False`, take the appropriate branch
- Otherwise, keep `ite` symbolic (let the simulator handle case-splitting)

## Architecture

### Input Requirements

- Terms must be maximally shared via `shareCommon` like every other module in `Sym`.
- Enables pointer-based cache keys throughout

### Integration with SymM

`SimpM` is designed to work within the `SymM` symbolic simulation framework:
- Uses `BackwardRule` for control-flow (monadic bind, match, combinators)
- `SimpM` handles term simplification between control-flow steps
- Avoids entering control-flow binders
-/

/-- Configuration options for the structural simplifier. -/
structure Config where
  /-- Maximum number of steps that can be performed by the simplifier. -/
  maxSteps : Nat := 1000
  /--
  Maximum depth of reentrant simplifier calls through dischargers.
  Prevents infinite loops when conditional rewrite rules trigger recursive discharge attempts.
  -/
  maxDischargeDepth : Nat := 2

/--
The result of simplifying an expression `e`.

The `done` flag controls whether simplification should continue after this result:
- `done = false` (default): Continue with subsequent simplification steps
- `done = true`: Stop processing, return this result as final

## Use cases for `done = true`

### In `pre` simprocs
Skip simplification of certain subterms entirely:
```
def skipLambdas : Simproc := fun e =>
  if e.isLambda then return .rfl (done := true)
  else return .rfl
```

### In `post` simprocs
Perform single-pass normalization without recursive simplification:
```
def singlePassNormalize : Simproc := fun e =>
  if let some (e', h) ← tryNormalize e then
    return .step e' h (done := true)
  else return .rfl
```
With `done = true`, the result `e'` won't be recursively simplified.

## Behavior

The `done` flag affects:
1. **`andThen` composition**: If the first simproc returns `done = true`,
   the second simproc is skipped.
2. **Recursive simplification**: After `pre` or `post` returns `.step e' h`,
   `simp` normally recurses on `e'`. With `done = true`, recursion is skipped.

The flag is orthogonal to caching: both `.rfl` and `.step` results are cached
regardless of the `done` flag, and cached results are always treated as final.
-/
inductive Result where
  /-- No change. If `done = true`, skip remaining simplification steps for this term. -/
  | rfl (done : Bool := false)
  /--
  Simplified to `e'` with proof `proof : e = e'`.
  If `done = true`, skip recursive simplification of `e'`. -/
  | step (e' : Expr) (proof : Expr) (done : Bool := false)
  deriving Inhabited

private opaque MethodsRefPointed : NonemptyType.{0}
def MethodsRef : Type := MethodsRefPointed.type
instance : Nonempty MethodsRef := by exact MethodsRefPointed.property

/-- Read-only context for the simplifier. -/
structure Context where
  /-- Simplifier configuration options. -/
  config : Config := {}
  /-- Size of the local context when simplification started.
  Used to determine which free variables were introduced during simplification. -/
  initialLCtxSize : Nat
  dischargeDepth  : Nat := 0

/-- Cache mapping expressions (by pointer equality) to their simplified results. -/
abbrev Cache := PHashMap ExprPtr Result

/-- Mutable state for the simplifier. -/
structure State where
  /--
  Cache of previously simplified expressions to avoid redundant work.
  **Note**: Consider moving to `SymM.State`
  -/
  cache : Cache := {}
  /-- Stack of free variables available for reuse when re-entering binders.
  Each entry is (type pointer, fvarId). -/
  binderStack : List (ExprPtr × FVarId) := []
  /-- Number of steps performed so far. -/
  numSteps := 0
  /-- Cache for generated funext theorems -/
  funext : PHashMap ExprPtr Expr := {}

/-- Monad for the structural simplifier, layered on top of `SymM`. -/
abbrev SimpM := ReaderT MethodsRef $ ReaderT Context StateRefT State SymM

instance : Inhabited (SimpM α) where
  default := throwError "<default>"

abbrev Simproc := Expr → SimpM Result

structure Methods where
  pre        : Simproc  := fun _ => return .rfl
  post       : Simproc  := fun _ => return .rfl
  /--
  `wellBehavedMethods` must **not** be set to `true` IF their behavior
  depends on new hypotheses in the local context. For example, for applying
  conditional rewrite rules.
  Reason: it would prevent us from aggressively caching `simp` results.
  -/
  wellBehavedMethods : Bool := true
  deriving Inhabited

unsafe def Methods.toMethodsRefImpl (m : Methods) : MethodsRef :=
  unsafeCast m

@[implemented_by Methods.toMethodsRefImpl]
opaque Methods.toMethodsRef (m : Methods) : MethodsRef

unsafe abbrev MethodsRef.toMethodsImpl (m : MethodsRef) : Methods :=
  unsafeCast m

@[implemented_by MethodsRef.toMethodsImpl]
opaque MethodsRef.toMethods (m : MethodsRef) : Methods

def getMethods : SimpM Methods :=
  return MethodsRef.toMethods (← read)

/-- Runs a `SimpM` computation with the given theorems and configuration. -/
def SimpM.run (x : SimpM α) (methods : Methods := {}) (config : Config := {}) : SymM α := do
  let initialLCtxSize := (← getLCtx).decls.size
  x methods.toMethodsRef { initialLCtxSize, config } |>.run' {}

@[extern "lean_sym_simp"] -- Forward declaration
opaque simp : Simproc

def getConfig : SimpM Config :=
  return (← readThe Context).config

abbrev getCache : SimpM Cache :=
  return (← get).cache

abbrev pre : Simproc := fun e => do
  (← getMethods).pre e

abbrev post : Simproc := fun e => do
  (← getMethods).post e

abbrev withoutModifyingCache (k : SimpM α) : SimpM α := do
  let cache ← getCache
  try k finally modify fun s => { s with cache }

abbrev withoutModifyingCacheIfNotWellBehaved (k : SimpM α) : SimpM α := do
  if (← getMethods).wellBehavedMethods then k else withoutModifyingCache k

end Simp

abbrev simp (e : Expr) (methods :  Simp.Methods := {}) (config : Simp.Config := {}) : SymM Simp.Result := do
  Simp.SimpM.run (Simp.simp e) methods config

end Lean.Meta.Sym
