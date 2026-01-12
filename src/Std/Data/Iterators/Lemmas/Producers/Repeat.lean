/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Std.Data.Iterators.Producers.Repeat
public import Init.Data.Iterators.Lemmas.Combinators.Take

@[expose] public section

namespace Std
open Std.Iterators

variable {α : Type w} {f : α → α} {init : α}

theorem Iter.step_repeat :
    (Iter.repeat f init).step = .yield (Iter.repeat f (f init)) init ⟨rfl, rfl⟩ := by
  simp [Iter.«repeat», Iter.step, Iter.toIterM, IterM.step, Iterator.step, IterM.toIter]

theorem Iter.atIdxSlow?_zero_repeat :
    (Iter.repeat f init).atIdxSlow? 0 = some init := by
  rw [atIdxSlow?, step_repeat]

theorem Iter.atIdxSlow?_succ_repeat {k : Nat} :
    (Iter.repeat f init).atIdxSlow? (k + 1) = (Iter.repeat f (f init)).atIdxSlow? k := by
  rw [atIdxSlow?, step_repeat]

theorem Iter.atIdxSlow?_succ_repeat_eq_map {k : Nat} :
    (Iter.repeat f init).atIdxSlow? (k + 1) = f <$> ((Iter.repeat f init).atIdxSlow? k) := by
  rw [atIdxSlow?, step_repeat]
  simp only
  induction k generalizing init
  · simp [atIdxSlow?_zero_repeat, Functor.map]
  · simp [*, atIdxSlow?_succ_repeat]

@[simp]
theorem Iter.atIdxSlow?_repeat {n : Nat} :
    (Iter.repeat f init).atIdxSlow? n = some (Nat.repeat f n init) := by
  induction n generalizing init
  · apply atIdxSlow?_zero_repeat
  · rename_i _ ih
    simp [atIdxSlow?_succ_repeat_eq_map, ih, Nat.repeat]

theorem Iter.isSome_atIdxSlow?_repeat {k : Nat} :
    ((Iter.repeat f init).atIdxSlow? k).isSome := by
  induction k generalizing init <;> simp [*]

@[simp]
theorem Iter.toList_take_repeat_succ {k : Nat} :
    ((Iter.repeat f init).take (k + 1)).toList = init :: ((Iter.repeat f (f init)).take k).toList := by
  rw [toList_eq_match_step, step_take, step_repeat]

end Std
