/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.SymM

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

**Maintaining `maxFVar`:** The mapping is updated during `intro`. The default `intro` in `MetaM` uses
`instantiate` to replace `Expr.bvar` with `Expr.fvar`, using `looseBVarRange` to skip subexpressions
without relevant bound variables. The `SymM` version piggybacks on this traversal to update `maxFVar`.

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

### A syntactic definitional equality test

**The problem:** The `isDefEq` predicate in `MetaM` is optimized for elaboration and user-facing tactics.
It supports reduction, type-class resolution, and many other features that can be expensive or have
unpredictable running time. For symbolic simulation, where `isDefEq` is called frequently, this can
cause unexpected slowdowns.

**The solution:** In `SymM`, the definitional equality test is optimized for the syntactic case. It avoids
expensive steps such as lazy-delta reduction. Reduction rules such as `beta` are implemented with term
size and algorithmic complexity in mind, ensuring predictable performance.

### `GrindM` state

**The problem:** In symbolic simulation, we often want to discharge many goals using proof automation such
as `grind`. Many of these goals share very similar local contexts. If we invoke `grind` on each goal
independently, we repeatedly reprocess the same hypotheses.

**The solution:** In `SymM`, we carry the `GrindM` state across goals and use `Grind.Goal` instead of
bare metavariables. We also provide APIs for incrementally processing local declarations, so hypotheses
are only processed once.

-/
