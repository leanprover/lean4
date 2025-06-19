/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Init.Data.Iterators.Basic
import Init.Data.Iterators.Consumers
import Init.Data.Iterators.PostconditionMonad
import Init.Data.Iterators.Internal
import Std.Data.Iterators.Producers
import Std.Data.Iterators.Combinators
import Std.Data.Iterators.Lemmas

/-!
# Iterators

The `Std.Data.Iterators` module provides a uniform abstraction over data that can be iterated over
in a sequential way, with a focus on convenience and efficiency. It is heavily inspired by Rust's
iterator library and Haskell's `streamly`.

An iterator is an abstraction of a sequence of values that may or may not terminate. For example,
every list can be traversed with an iterator via `List.iter`.

Most users of the iterator API will just put together existing library functions that
create, combine and consume iterators. Consider a simple example:

```lean
-- [1, 2, 3].iter : Iter (α := ListIterator α) Nat (α being implicit)
#check [1, 2, 3].iter

-- 12
#eval [1, 2, 3].iter.map (· * 2) |>.fold (init := 0) (· + ·)
```

An iterator that emits values in `β` is an element of the type `Iter (α := ?) β`. The implicit
type argument `α` contains stateful information about the iterator. `IterM (α := ?) m β` represents
iterators over a monad `m`. In both cases, the implementation is provided by a typeclass
`Iterator α m β`, where `m` is a monad in which the iteration happens.

The heart of an iterator `it : Iter β` is its `it.step` function, which returns `it.Step α β`.
Here, `it.Step` is a type that either (1) provides an output value in `β` and a
successor iterator (`yield`), (2) provides only a successor iterator with no output (`skip`), or
(3) signals that the iterator has finished and will provide no more outputs (`done`).
For technical reasons related to termination proofs, the returned `it.Step` also contains proof
that it is a "plausible" step obtained from `it`.

The `step` function can also be used by hand:

```lean
def sumrec (l : List Nat) : Nat :=
  go (l.iter.map (2 * ·)) 0
where
  go it acc :=
    match it.step with
    | .yield it' n _ => go it' (acc + n)
    | .skip it' _ => go it' acc
    | .done _ => acc
  termination_by it.finitelyManySteps
```

In general, iterators do not need to terminate after finitely many steps. This example
works because the iterator type at hand has an instance of the `Std.Iterators.Finite` typeclass.
Iterators that may not terminate but will not end up in an infinite sequence of `.skip`
steps are called productive. This behavior is encoded in the `Std.Iterators.Productive` typeclass.

## Stability

The API for the usage of iterators provided in this module can be considered stable, as well as
the API for the verification of programs using iterators, unless explicitly stated otherwise.

Contrarily, the API for implementation of new iterators, including the design of the `Iterator`
typeclass, is still experimental and will change in the future. It is already planned that there
will be a breaking change to make the iterators more flexible with regard to universes, a change
that needs to wait for a language feature.

## Module structure

A distinction that cuts through the whole module is that between pure and monadic
iterators. Each submodule contains a dedicated `Monadic` sub-submodule.

Depending on whether functionality is needed in `Init`, modules might exist in `Init` or in `Std`.
The following module names can then be found under `Init.Data.Iterators`, `Std.Data.Iterators` or
both.

### Basic iterator API

* `Basic` defines `Iter` and `IterM` as well as `Iterator`, `Finite`
  and `Productive` typeclasses.
* `Producers` provides iterator implementations for common data types.
* `Consumers` provides functions that take one or more iterators, iterate over them and potentially
  return some result. Examples are the `toList` function and an instance for the `ForIn` typeclass.
  These operations allow for what is also known as *internal iteration*, where the caller delegates
  the control flow during the iteration to the called consumer.
* `Combinators` will provide operations that transform one or more iterators into a new iterator
  as soon as the first such combinator has been implemented.

### Verification API

`Lemmas` provides the means to verify programs that use iterators.

In particular, `Lemmas.Equivalence` develops the theory of equivalences of iterators.

### Implementation details

`Internal` contains code that should not be relied upon because it may change in the future.
This whole module is explicitly experimental and it is not advisable for downstream users to
expect stability to implement their own iterators at this point in time.

-/
