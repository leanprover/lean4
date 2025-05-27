/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Init.Data.Option.Lemmas
import Std.Data.Iterators.Producers.Unfold
import Std.Data.Iterators.Consumers.Access
import Std.Data.Iterators.Consumers.Collect
import Std.Data.Iterators.Combinators.Take
import Std.Data.Iterators.Lemmas.Combinators.Take

namespace Std.Iterators

variable {α : Type w} {init : α} {f : α → α}

theorem Iter.step_unfold :
    (Iter.unfold init f).step = .yield (Iter.unfold (f init) f) init ⟨rfl, rfl⟩ := by
  rfl

@[simp]
theorem Iter.atIdxSlow?_zero_unfold :
    (Iter.unfold init f).atIdxSlow? 0 = some init := by
  rw [atIdxSlow?, step_unfold]

theorem Iter.atIdxSlow?_succ_unfold {k : Nat} :
    (Iter.unfold init f).atIdxSlow? (k + 1) = (Iter.unfold (f init) f).atIdxSlow? k := by
  rw [atIdxSlow?, step_unfold]

theorem Iter.atIdxSlow?_succ_unfold_eq_apply {k : Nat} :
    (Iter.unfold init f).atIdxSlow? (k + 1) = f <$> ((Iter.unfold init f).atIdxSlow? k) := by
  rw [atIdxSlow?, step_unfold]
  simp only
  induction k generalizing init
  · simp [Functor.map]
  · simp [*, atIdxSlow?_succ_unfold]

theorem Iter.isSome_atIdxSlow?_unfold {k : Nat} :
    ((Iter.unfold init f).atIdxSlow? k).isSome := by
  induction k generalizing init <;> simp [*, atIdxSlow?_succ_unfold]

theorem Iter.get_atIdxSlow?_succ_unfold {k : Nat} :
    ((Iter.unfold init f).atIdxSlow? (k + 1)).get isSome_atIdxSlow?_unfold =
      ((Iter.unfold (f init) f).atIdxSlow? k).get isSome_atIdxSlow?_unfold := by
  simp [Iter.atIdxSlow?_succ_unfold]

theorem Iter.get_atIdxSlow?_succ_unfold_eq_apply {k : Nat} :
    ((Iter.unfold init f).atIdxSlow? (k + 1)).get isSome_atIdxSlow?_unfold =
      f (((Iter.unfold init f).atIdxSlow? k).get isSome_atIdxSlow?_unfold) := by
  induction k generalizing init
  · simp [atIdxSlow?_succ_unfold]
  · simp [atIdxSlow?_succ_unfold_eq_apply, Functor.map, Option.eq_some_iff_get_eq]

theorem Iter.toList_take_unfold_succ {k : Nat} :
    ((Iter.unfold init f).take (k + 1)).toList = init :: ((Iter.unfold (f init) f).take k).toList := by
  rw [toList_eq_match_step, step_take, step_unfold]

end Std.Iterators
