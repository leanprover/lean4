/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Util.Cycle
public import Lake.Util.Store
public import Lake.Util.EquipT

/-!
# Topological / Suspending Recursive Builder

This module defines a recursive build function that topologically
(ι.e., via a depth-first search with memoization) builds the elements of
a build store.

This is called a suspending scheduler in *Build systems à la carte*.
-/

namespace Lake

/-!
## Recursive Fetching

In this section, we define the primitives that make up a builder.
-/

/--
A dependently typed monadic *fetch* function.

That is, a function within the monad `m` and takes an input `a : α`
describing what to fetch and produces some output `b : β a` (dependently
typed) or `b : B` (not) describing what was fetched. All build functions are
fetch functions, but not all fetch functions need build something.
-/
public abbrev DFetchFn (α : Type u) (β : α → Type v) (m : Type v → Type w) :=
  (a : α) → m (β a)

/-- A `DFetchFn` that is not dependently typed. -/
public abbrev FetchFn (α : Type u) (β : Type v) (m : Type v → Type w) :=
  α → m β

/-!
In order to nest builds / fetches within one another,
we equip the monad `m` with a fetch function of its own.
-/

/-- A transformer that equips a monad with a `DFetchFn`. -/
public abbrev DFetchFnT (α : Type u) (β : α → Type v) (m : Type v → Type w) :=
  EquipT (DFetchFn α β m) m

/-- A `DFetchFnT` that is not dependently typed. -/
public abbrev FetchFnT (α : Type u) (β : Type v) (m : Type v → Type w) :=
  DFetchFnT α (fun _ => β) m

/-!
We can then use the such a monad as the basis for a fetch function itself.
-/

/--
A `DFetchFn` that utilizes another `DFetchFn` equipped to the monad to
fetch values. It is thus usually implemented recursively via some variation
of the `recFetch` function below, hence the "rec" in both names.
-/
public abbrev DRecFetchFn (α : Type u) (β : α → Type v) (m : Type v → Type w) :=
  DFetchFn α β (DFetchFnT α β m)

/-- A `DRecFetchFn` that is not dependently typed. -/
public abbrev RecFetchFn (α : Type u) (β : Type v) (m : Type v → Type w) :=
  α → FetchFnT α β m β

/-- A `DFetchFn` that provides its base `DRecFetchFn` with itself. -/
@[specialize] public partial def recFetch
  [(α : Type u) → Nonempty (m α)] (fetch : DRecFetchFn α β m)
: DFetchFn α β m := fun a => fetch a |>.run (recFetch fetch)

/-!
The basic `recFetch` can fail to terminate in a variety of ways,
it can even cycle (i.e., `a` fetches `b` which fetches `a`). Thus, we
define the `acyclicRecFetch` below to guard against such cases.
-/

/--
A `recFetch` augmented by a `MonadCycle` to guard against recursive cycles.
If the set of visited keys is finite, this function should provably terminate.

We use `keyOf` to the derive the unique key of a fetch from its descriptor
`a : α`. We do this because descriptors may not be comparable and/or contain
more information than necessary to determine uniqueness.
-/
@[specialize] public def recFetchAcyclic
  [BEq κ] [Monad m] [MonadCycle κ m]
  (keyOf : α → κ) (fetch : DRecFetchFn α β m)
: DFetchFn α β m :=
  recFetch fun a => .mk fun recurse => guardCycle (keyOf a) do
    /-
    NOTE: We provide the stack directly to `recurse` rather than
    using the version in the monad to prevent it being overridden by
    the `fetch` function (and thereby potentially produce a cycle).
    -/
    let stack ← getCallStack
    fetch a |>.run fun a => withCallStack stack (recurse a)

/-!
When building, we usually do not want to build the same thing twice during
a single build pass. At the same time, separate builds may both wish to fetch
the same thing. Thus, we need to store past build results to return them upon
future fetches. This is what `recFetchMemoize` below does.
-/

/--
`recFetchAcyclic` augmented with a `MonadDStore` to
memoize fetch results and thus avoid computing the same result twice.
-/
@[specialize] public def recFetchMemoize
  [BEq κ] [Monad m] [MonadCycle κ m] [MonadDStore κ β m]
  (keyOf : α → κ) (compute : DRecFetchFn α (fun a => β (keyOf a)) m)
: DFetchFn α (fun a => β (keyOf a)) m :=
  inline <| recFetchAcyclic keyOf fun a =>
    fetchOrCreate (keyOf a) (compute a)
