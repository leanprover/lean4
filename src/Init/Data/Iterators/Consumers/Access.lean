/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
import Init.Data.Iterators.Consumers.Partial

namespace Std.Iterators

/--
If possible, takes `n` steps with the iterator `it` and
returns the `n`-th emitted value, or `none` if `it` finished
before emitting `n` values.

This function requires a `Productive` instance proving that the iterator will always emit a value
after a finite number of skips. If the iterator is not productive or such an instance is not
available, consider using `it.allowNontermination.atIdxSlow?` instead of `it.atIdxSlow?`. However,
it is not possible to formally verify the behavior of the partial variant.
-/
@[specialize]
def Iter.atIdxSlow? {α β} [Iterator α Id β] [Productive α Id]
    (n : Nat) (it : Iter (α := α) β) : Option β :=
  match it.step with
  | .yield it' out _ =>
    match n with
    | 0 => some out
    | k + 1 => it'.atIdxSlow? k
  | .skip it' _ => it'.atIdxSlow? n
  | .done _ => none
termination_by (n, it.finitelyManySkips)

/--
If possible, takes `n` steps with the iterator `it` and
returns the `n`-th emitted value, or `none` if `it` finished
before emitting `n` values.

This is a partial, potentially nonterminating, function. It is not possible to formally verify
its behavior. If the iterator has a `Productive` instance, consider using `Iter.atIdxSlow?` instead.
-/
@[specialize]
partial def Iter.Partial.atIdxSlow? {α β} [Iterator α Id β] [Monad Id]
    (n : Nat) (it : Iter.Partial (α := α) β) : Option β := do
  match it.it.step with
  | .yield it' out _ =>
    match n with
    | 0 => some out
    | k + 1 => (⟨it'⟩ : Iter.Partial (α := α) β).atIdxSlow? k
  | .skip it' _ => (⟨it'⟩ : Iter.Partial (α := α) β).atIdxSlow? n
  | .done _ => none

end Std.Iterators
