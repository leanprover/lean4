/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Consumers.Loop
public import Init.Data.Iterators.Consumers.Monadic.Access

set_option linter.missingDocs true

@[expose] public section

namespace Std
open Std.Iterators

/--
If possible, takes `n` steps with the iterator `it` and
returns the `n`-th emitted value, or `none` if `it` finished
before emitting `n` values.

If the iterator is not productive, this function might run forever in an endless loop of iterator
steps. The variant `it.ensureTermination.atIdxSlow?` is guaranteed to terminate after finitely many
steps.
-/
@[specialize]
def Iter.atIdxSlow? {α β} [Iterator α Id β]
    (n : Nat) (it : Iter (α := α) β) : Option β :=
  WellFounded.extrinsicFix₂ (C₂ := fun _ _ => Option β) (α := Iter (α := α) β) (β := fun _ => Nat)
    (InvImage
      (Prod.Lex WellFoundedRelation.rel IterM.TerminationMeasures.Productive.Rel)
      (fun p => (p.2, p.1.finitelyManySkips!)))
    (fun it n recur =>
      match it.step with
      | .yield it' out _ =>
        match n with
        | 0 => some out
        | k + 1 => recur it' k (by decreasing_tactic)
      | .skip it' _ => recur it' n (by decreasing_tactic)
      | .done _ => none) it n

/--
If possible, takes `n` steps with the iterator `it` and
returns the `n`-th emitted value, or `none` if `it` finished
before emitting `n` values.

This variant terminates after finitely many steps and requires a proof that the iterator is
finite. If such a proof is not available, consider using `Iter.toArray`.
-/
@[inline]
def Iter.Total.atIdxSlow? {α β} [Iterator α Id β] [Monad Id] [Productive α Id]
    (n : Nat) (it : Iter.Total (α := α) β) : Option β :=
  it.it.atIdxSlow? n

@[inline, inherit_doc Iter.atIdxSlow?, deprecated Iter.atIdxSlow? (since := "2026-01-28")]
def Iter.Partial.atIdxSlow? {α β} [Iterator α Id β] [Monad Id]
    (n : Nat) (it : Iter.Partial (α := α) β) : Option β :=
  it.it.atIdxSlow? n

@[always_inline, inline, inherit_doc IterM.atIdx?]
def Iter.atIdx? {α β} [Iterator α Id β] [IteratorAccess α Id]
    (n : Nat) (it : Iter (α := α) β) : Option β :=
  match (IteratorAccess.nextAtIdx? it.toIterM n).run.val with
  | .yield _ out => some out
  | .skip _ => none
  | .done => none

end Std
