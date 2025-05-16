/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Std.Data.Iterators.Consumers.Partial

namespace Std.Iterators

@[specialize]
def Iter.seekIdx? {α β} [Iterator α Id β] [Productive α Id]
    (n : Nat) (it : Iter (α := α) β) : Option β :=
  match it.step with
  | .yield it' out _ =>
    match n with
    | 0 => some out
    | k + 1 => it'.seekIdx? k
  | .skip it' _ => it'.seekIdx? n
  | .done _ => none
termination_by (n, it.finitelyManySkips)

@[specialize]
partial def Iter.Partial.seekIdx? {α β} [Iterator α Id β] [Monad Id]
    (n : Nat) (it : Iter.Partial (α := α) β) : Option β := do
  match it.it.step with
  | .yield it' out _ =>
    match n with
    | 0 => some out
    | k + 1 => (⟨it'⟩ : Iter.Partial (α := α) β).seekIdx? k
  | .skip it' _ => (⟨it'⟩ : Iter.Partial (α := α) β).seekIdx? n
  | .done _ => none

end Std.Iterators
