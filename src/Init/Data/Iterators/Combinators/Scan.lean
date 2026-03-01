/-
Copyright (c) 2025 Chad Sharp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chad Sharp
-/

module

prelude
public import Init.Data.Iterators.Combinators.Monadic.Scan
import Init.Data.Iterators.Combinators.FilterMap

@[expose] public section

/-!

# `scan`, `scanM` and `scanWithPostcondition` combinators

This file provides iterator combinators for scanning with an accumulator.

* `Iter.scan` threads an accumulator through the iterator using a pure stepping function.
* `Iter.scanM` threads an accumulator using a monadic stepping function.
* `Iter.scanWithPostcondition` threads an accumulator using a monadic stepping function
  whose result is returned as a subtype.
-/

namespace Std
open Iterators.Types Std.Iterators
variable {α β γ : Type w}

-- We cannot use `inherit_doc` because the docstring for `IterM` states that a `MonadLiftT` instance
-- is needed.
/--
*Note: This is a very general combinator that requires an advanced understanding of monads,
dependent types and termination proofs. The variants `scan` and `scanM` are easier to use
and sufficient for most use cases.*

If `it` is an iterator, then `it.scanWithPostcondition f acc` is another iterator that applies a
monadic function `f` to accumulate values emitted by `it`. It first emits the initial accumulator
`acc`, then for each value `b` emitted by `it`, it computes `f acc b` and emits the result.

`f` is expected to return `PostconditionT n γ`, where `n` is an arbitrary monad.
The `PostconditionT` transformer allows the caller to intrinsically prove properties about
`f`'s return value in the monad `n`, enabling termination proofs depending on the specific behavior
of `f`.

**Marble diagram (without monadic effects):**

```text
it                          ---a ---b ---c ---⊥
it.scanWithPostcondition    -i -a'-ab'-abc'---⊥
```

(given that `a' ← f i a'`, `ab' ← f a' b`, `abc' ← f ab' c'`)

**Termination properties:**

* `Finite` instance: only if `it` is finite
* `Productive` instance: only if `it` is productive

For certain stepping functions `f`, the resulting iterator will be finite even though
no `Finite` instance is provided. For example, if `f` is an `ExceptT` monad and will always fail,
then `it.scanWithPostcondition` will be finite even if `it` isn't.

In such situations, the missing instances can be proved manually if the postcondition bundled in
the `PostconditionT n` monad is strong enough. In the given example, a suitable postcondition might
be `fun _ => False`.

**Performance:**

For each value emitted by the base iterator `it`, this combinator calls `f`.
-/
@[inline]
def Iter.scanWithPostcondition {m : Type w → Type w'} [Monad m]
    (f : γ → β → PostconditionT m γ) (acc : γ) (it : Iter (α := α) β) :=
  it.toIterM.scanWithPostcondition f acc

/--
If `it` is an iterator, then `it.scanM f acc` is another iterator that applies a monadic
function `f` to accumulate values emitted by `it`. It first emits the initial accumulator
`acc`, then for each value `b` emitted by `it`, it computes `f acc b` and emits the result.

If `f` is pure, then the simpler variant `it.scan` can be used instead.

**Marble diagram (without monadic effects):**

```text
it           ---a ---b ---c ---⊥
it.scanM     -i -a'-ab'-abc'---⊥
```

(given that `a' ← f i a`, `ab' ← f a' b`, `abc' ← f ab' c`)

**Termination properties:**

* `Finite` instance: only if `it` is finite
* `Productive` instance: only if `it` is productive

For certain stepping functions `f`, the resulting iterator will be finite even though
no `Finite` instance is provided. For example, if `f` is an `ExceptT` monad and will always fail,
then `it.scanM` will be finite even if `it` isn't. In such cases, the termination proof needs
to be done manually.

**Performance:**

For each value emitted by the base iterator `it`, this combinator calls `f`.
-/
@[inline]
def Iter.scanM {n : Type w → Type w''} [MonadAttach n] [MonadLiftT Id n]
    (f : γ → β → n γ) (acc : γ) (it : Iter (α := α) β) :=
  it.toIterM.scanM f acc

@[inline, inherit_doc IterM.scan]
def Iter.scan (f : γ → β → γ) (acc : γ) (it : Iter (α := α) β) :=
  it.toIterM.scan f acc |>.toIter

end Std
