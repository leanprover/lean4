/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.Range.Basic
import Init.Data.List.Range
import Init.Data.Int.DivModLemmas

theorem Nat.pos_of_div_pos {a b : Nat} (h : 0 < a / b) : 0 < a := by
  cases b with
  | zero => simp at h
  | succ b =>
    match a, h with
    | 0, h => simp at h
    | a + 1, _ => exact zero_lt_succ a

namespace Std.Range

/-- The number of elements in the range. -/
def size (r : Range) : Nat := (r.stop - r.start) / r.step

theorem mem_of_mem_range' (r : Range) (h : x ∈ List.range' r.start r.size r.step) : x ∈ r := by
  obtain ⟨i, h', rfl⟩ := List.mem_range'.1 h
  refine ⟨Nat.le_add_right .., ?_⟩
  unfold size at h'
  have := r.step_pos
  have h₁ : 0 < (r.stop - r.start) / r.step := by omega
  have h₂ : 0 < r.stop - r.start := Nat.pos_of_div_pos h₁
  constructor
  · calc
      _ < r.start + r.step * ((r.stop - r.start) / r.step) :=
            Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_left h' r.step_pos) r.start
      _ ≤ r.start + (r.stop - r.start) :=
            Nat.add_le_add_left (Nat.mul_div_le (r.stop - r.start) r.step) r.start
      _ ≤ r.stop := by omega
  · rw [Nat.add_comm, Nat.add_sub_cancel, Nat.mul_mod_right]

theorem forIn'_loop_eq_forIn'_range' [Monad m] (r : Std.Range)
    (init : β) (f : (a : Nat) → a ∈ r → β → m (ForInStep β)) (i) (hi : (i - r.stop) % r.step = 0):
    forIn'.loop r f init i w₁ w₂ w₃ =
      (List.range' i ((r.stop - i) / r.step) r.step).forIn' init fun a h => f a sorry := by
  sorry

theorem forIn'_eq_forIn'_range' [Monad m] (r : Std.Range)
    (init : β) (f : (a : Nat) → a ∈ r → β → m (ForInStep β)) :
    forIn' r init f =
      forIn' (List.range' r.start r.size r.step) init (fun a h => f a (mem_of_mem_range' r h)) := by
  rcases r with ⟨start, stop, step, step_pos⟩
  simp [size]
  simp only [forIn', Range.forIn']
where
  go (start stop step step_pos) (f) (init) (w₁ w₂ w₃) (w₄) (w₅) :
    forIn'.loop ⟨start, stop, step, step_pos⟩ f init start w₁ w₂ w₃ =
      forIn (List.pmap Subtype.mk (List.range' start ((stop - start) / step) step) w₄) init fun x => f x.val w₅ := by
    sorry



theorem forIn_eq_forIn_range' [Monad m] (r : Std.Range)
    (init : β) (f : Nat → β → m (ForInStep β)) :
    forIn r init f = forIn (List.range' r.start r.numElems r.step) init f := by
  refine Eq.trans ?_ <| (forIn'_eq_forIn_range' r init (fun x _ => f x)).trans ?_
  · simp [forIn, forIn']
  · suffices ∀ L H, forIn (List.pmap Subtype.mk L H) init (f ·.1) = forIn L init f from this _ ..
    intro L; induction L generalizing init <;> intro H <;> simp [*]

end Std.Range
