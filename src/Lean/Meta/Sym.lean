/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.AlphaShareBuilder
public import Lean.Meta.Sym.AlphaShareCommon
public import Lean.Meta.Sym.ExprPtr
public import Lean.Meta.Sym.SymM
public import Lean.Meta.Sym.MaxFVar
public import Lean.Meta.Sym.ReplaceS
public import Lean.Meta.Sym.LooseBVarsS
public import Lean.Meta.Sym.InstantiateS
public import Lean.Meta.Sym.IsClass
public import Lean.Meta.Sym.Intro
public import Lean.Meta.Sym.InstantiateMVarsS
public import Lean.Meta.Sym.ProofInstInfo
public import Lean.Meta.Sym.AbstractS
public import Lean.Meta.Sym.Pattern
public import Lean.Meta.Sym.Apply
public import Lean.Meta.Sym.InferType
public import Lean.Meta.Sym.Simp
public import Lean.Meta.Sym.Util

/-!
# Symbolic simulation support.

This module provides `SymM`, a monad for implementing symbolic simulators (e.g., verification condition generators)
using Lean. The monad addresses performance issues found in symbolic simulators built on top of user-facing
tactics (e.g., `apply` and `intros`).

## Overview

The `SymM` monad provides an alternative to tactics built using the `MetaM` monad. Goals are still represented
by metavariables, but with restrictions that enable more efficient implementations. For example, we cannot
revert or clear local declarations. This simpler metavariable management reduces the complexity of key
operations from O(n log n) to O(1). The definitional equality test is more syntactic and cheaper than
the one available in `MetaM`. `SymM` also provides functions for efficiently discharging goals using `GrindM`.

## Design decisions

### No `revert` or `clear`

In `SymM`, you cannot revert or clear local declarations, so local contexts grow monotonically.
Each goal is represented by a `Grind.Goal` object which includes a metavariable.

**Why this restriction?** In standard `MetaM`, validating a metavariable assignment `?m := e` requires
traversing `e`, checking free variables occurring in `e`, and checking that every nested metavariable
`?n` in `e` has a local context compatible with `?m`'s local context. This uses `LocalContext.isSubPrefixOf`,
which traverses two `PersistentArray`s with O(log n) lookups per element, expensive when called frequently.

**The key insight:** Since free variable indices increase monotonically and are never reused, a local
context can be identified by its maximal free variable index. To check whether `lctx₁` is a sub-prefix
of `lctx₂`, we only need to verify that `lctx₂` contains the maximal free variable declared in `lctx₁`.

**Implementation:** We maintain a mapping `maxFVar` from expressions to free variables, where `maxFVar[e] = x`
means `x` is the free variable with maximal index occurring in `e`. When assigning `?m := e`, we check
whether `maxFVar[e]` is in `?m.lctx` — a single hash lookup, O(1).

**Maintaining `maxFVar`:** The mapping is automatically updated when we use `getMaxFVar?`.

### Structural matching and definitional equality

**The problem:** The `isDefEq` predicate in `MetaM` is designed for elaboration and user-facing tactics.
It supports reduction, type-class resolution, and many other features that can be expensive or have
unpredictable running time. For symbolic simulation, where pattern matching is called frequently on
large ground terms, these features become performance bottlenecks.

**The solution:** In `SymM`, pattern matching and definitional equality are restricted to a more syntactic,
predictable subset. Key design choices:

1. **Reducible declarations are abbreviations.** Reducible declarations are eagerly expanded when indexing
   terms and when entering symbolic simulation mode. During matching, we assume abbreviations have already
   been expanded.

  **Why `MetaM` `simp` cannot make this assumption**: The simplifier in `MetaM` is designed for interactive use,
  where users want to preserve their abstractions. Even reducible definitions may represent meaningful
  abstractions that users may not want unfolded. For example, when applying `simp` to `x ≥ y`, users
  typically do not want it transformed to `y ≤ x` just because `GE.ge` is a reducible abbreviation.

2. **Proofs are ignored.** We skip proof arguments during matching due to proof irrelevance. Proofs are
   "noisy": they are typically built using different automation or manually, so we can have radically
   different proof terms for the same trivial fact.

3. **Instances are ignored.** Lean's class hierarchy contains many diamonds. For example, `Add Nat` can be
   obtained directly from the `Nat` library or derived from the fact that `Nat` is a `Semiring`. Proof
   automation like `grind` attempts to canonicalize instances, but this is expensive. Instead, we treat
   instances as support terms and skip them during matching, and we check them later using the standard
   definitionally equality test in a mode where only reducible and instance declarations are unfolded.

   **The implicit assumption:** If two terms have the same instance type, they are definitionally equal.
   This holds in well-designed Lean code. For example, the `Add Nat` instance from the `Nat` library is
   definitionally equal to the one derived from `Semiring`, and this can be established by unfolding only
   reducible and instance declarations. Code that violates this assumption is considered misuse of Lean's
   instance system.

4. **Types must be indexed.** Unlike proofs and instances, types cannot be ignored, without indexing them,
   pattern matching produces too many candidates. Like other abbreviations, type abbreviations are expanded.
   Note that given `def Foo : Type := Bla`, the terms `Foo` and `Bla` are *not* considered structurally
   equal in the symbolic simulator framework.

### Skipping type checks on assignment

**The problem:** In `MetaM`, assigning `?m := v` requires checking that `typeof(?m)` is definitionally
equal to `typeof(v)`. This is necessary when metavariable types contain unassigned universe or expression
metavariables that must be constrained. For example, applying `Exists.intro.{?u} ?α ...` requires the
type check to constrain `?u`.

**The optimization:** When both types are ground (no unassigned metavariables), the check is redundant,
well-typed terms have unique types up to definitional equality, and the types were already checked when
the terms were constructed. `SymM` tracks whether types are ground and skips the check when possible.
Checks are also skipped when nothing new can be learned from them assuming terms are all well-typed.
For domain-specific constructors (e.g., `Exec.seq` in symbolic execution), types are typically ground,
so the check is almost always skipped.

### `GrindM` state

**The problem:** In symbolic simulation, we often want to discharge many goals using proof automation such
as `grind`. Many of these goals share very similar local contexts. If we invoke `grind` on each goal
independently, we repeatedly reprocess the same hypotheses.

**The solution:** In `SymM`, we carry the `GrindM` state across goals and use `Grind.Goal` instead of
bare metavariables. We also provide APIs for incrementally processing local declarations, so hypotheses
are only processed once.

-/
