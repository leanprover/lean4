/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Consumers.Monadic.Access
public import Init.Data.Iterators.Consumers.Partial
public import Init.Data.Iterators.Consumers.Total
public import Init.Ext
public import Init.WFExtrinsicFix

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

-- We provide the functional induction principle by hand because `atIdxSlow?` is implemented using
-- `extrinsicFix₂` and not using well-founded recursion.
/-
An induction principle for `Iter.atIdxSlow?`.

This lemma provides a functional induction principle for reasoning about `Iter.atIdxSlow? n it`.

The induction follows the structure of iterator steps.
- base case: when we reach the desired index (`n = 0`) and get a `.yield` step
- inductive case: when we have a `.yield` step but need to continue (`n > 0`)
- skip case: when we encounter a `.skip` step and continue with the same index
- done case: when the iterator is exhausted and we return `none`
-/
theorem Iter.atIdxSlow?.induct_unfolding {α β : Type u} [Iterator α Id β] [Productive α Id]
    (motive : Nat → Iter β → Option β → Prop)
    -- Base case: we have reached index 0 and found a value
    (yield_zero : ∀ (it it' : Iter (α := α) β) (out : β) (property : it.IsPlausibleStep (IterStep.yield it' out)),
        it.step = ⟨IterStep.yield it' out, property⟩ → motive 0 it (some out))
    -- Inductive case: we have a yield but need to continue to a higher index
    (yield_succ : ∀ (it it' : Iter (α := α) β) (out : β) (property : it.IsPlausibleStep (IterStep.yield it' out)),
        it.step = ⟨IterStep.yield it' out, property⟩ →
        ∀ (k : Nat), motive k it' (Iter.atIdxSlow? k it') → motive k.succ it (Iter.atIdxSlow? k it'))
    -- Skip case: we encounter a skip and continue with the same index
    (skip_case : ∀ (n : Nat) (it it' : Iter β) (property : it.IsPlausibleStep (IterStep.skip it')),
        it.step = ⟨IterStep.skip it', property⟩ →
        motive n it' (Iter.atIdxSlow? n it') → motive n it (Iter.atIdxSlow? n it'))
    -- Done case: the iterator is exhausted, return none
    (done_case : ∀ (n : Nat) (it : Iter β) (property : it.IsPlausibleStep IterStep.done),
        it.step = ⟨IterStep.done, property⟩ → motive n it none)
    -- The conclusion: the property holds for all indices and iterators
    (n : Nat) (it : Iter β) : motive n it (Iter.atIdxSlow? n it) := by
  simp only [atIdxSlow?] at *
  rw [WellFounded.extrinsicFix₂_eq_apply]
  · split
    · split
      · apply yield_zero <;> assumption
      · apply yield_succ
        all_goals try assumption
        apply Iter.atIdxSlow?.induct_unfolding <;> assumption
    · apply skip_case
      all_goals try assumption
      apply Iter.atIdxSlow?.induct_unfolding <;> assumption
    · apply done_case <;> assumption
  · exact InvImage.wf _ WellFoundedRelation.wf
termination_by (n, it.finitelyManySkips)

/--
If possible, takes `n` steps with the iterator `it` and
returns the `n`-th emitted value, or `none` if `it` finished
before emitting `n` values.

This variant terminates after finitely many steps and requires a proof that the iterator is
productive. If such a proof is not available, consider using `Iter.toArray`.
-/
@[inline]
def Iter.Total.atIdxSlow? {α β} [Iterator α Id β] [Productive α Id]
    (n : Nat) (it : Iter.Total (α := α) β) : Option β :=
  it.it.atIdxSlow? n

@[inline, inherit_doc Iter.atIdxSlow?, deprecated Iter.atIdxSlow? (since := "2026-01-28")]
def Iter.Partial.atIdxSlow? {α β} [Iterator α Id β]
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
