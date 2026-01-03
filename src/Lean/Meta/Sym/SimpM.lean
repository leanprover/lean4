/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.SymM
public import Lean.Meta.Sym.Pattern
import Lean.Meta.Sym.DiscrTree
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
  /-- If `true`, unfold let-bindings (zeta reduction) during simplification. -/
  zetaDelta : Bool := true
  /-- Maximum number of steps that can be performed by the simplifier. -/
  maxSteps : Nat := 0
  -- **TODO**: many are still missing

/-- The result of simplifying some expression `e`. -/
structure Result where
  /-- The simplified version of `e` -/
  expr           : Expr
  /-- A proof that `e = expr`, where the simplified expression is on the RHS.
  If `none`, the proof is assumed to be `refl`. -/
  proof?         : Option Expr := none

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

/-- Monad for the structural simplifier, layered on top of `SymM`. -/
abbrev SimpM := ReaderT MethodsRef $ ReaderT Context StateRefT State SymM

instance : Inhabited (SimpM α) where
  default := throwError "<default>"

abbrev Simproc := Expr → SimpM Result

structure Methods where
  pre        : Simproc  := fun e => return { expr := e }
  post       : Simproc  := fun e => return { expr := e }
  discharge? : Expr → SimpM (Option Expr) := fun _ => return none
  /--
  `wellBehavedDischarge` must **not** be set to `true` IF `discharge?`
  access local declarations with index >= `Context.lctxInitIndices` when
  `contextual := false`.
  Reason: it would prevent us from aggressively caching `simp` results.
  -/
  wellBehavedDischarge : Bool := true
  deriving Inhabited

unsafe def Methods.toMethodsRefImpl (m : Methods) : MethodsRef :=
  unsafeCast m

@[implemented_by Methods.toMethodsRefImpl]
opaque Methods.toMethodsRef (m : Methods) : MethodsRef

unsafe def MethodsRef.toMethodsImpl (m : MethodsRef) : Methods :=
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
opaque simp (e : Expr) : SimpM Result

def getConfig : SimpM Config :=
  return (← readThe Context).config

abbrev getCache : SimpM Cache :=
  return (← get).cache

abbrev pre (e : Expr) : SimpM Result := do
  (← getMethods).pre e

abbrev post (e : Expr) : SimpM Result := do
  (← getMethods).post e

end Simp

abbrev simp (e : Expr) (methods :  Simp.Methods := {}) (config : Simp.Config := {}) : SymM Simp.Result := do
  Simp.SimpM.run (Simp.simp e) methods config

end Lean.Meta.Sym
