/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix, Harun Khan
-/
prelude
import Init.Data.BitVec.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Fin.Iterate

set_option linter.missingDocs true

namespace BitVec

/--
iunfoldr is an iterative operation that applies a function `f` repeatedly.

It produces a sequence of state values `[s_0, s_1 .. s_w]` and a bitvector
`v` where `f i s_i = (s_{i+1}, b_i)` and `b_i` is bit `i`th least-significant bit
in `v` (e.g., `getLsb v i = b_i`).

Theorems involving `iunfoldr` can be eliminated using `iunfoldr_replace` below.
-/
def iunfoldr (f : Fin w -> α → α × Bool) (s : α) : α × BitVec w :=
  Fin.hIterate (fun i => α × BitVec i) (s, nil) fun i q =>
    (fun p => ⟨p.fst, cons p.snd q.snd⟩) (f i q.fst)

theorem iunfoldr.fst_eq
    {f : Fin w → α → α × Bool} (state : Nat → α) (s : α)
    (init : s = state 0)
    (ind : ∀(i : Fin w), (f i (state i.val)).fst = state (i.val+1)) :
    (iunfoldr f s).fst = state w := by
  unfold iunfoldr
  apply Fin.hIterate_elim (fun i (p : α × BitVec i) => p.fst = state i)
  case init =>
    exact init
  case step =>
    intro i ⟨s, v⟩ p
    simp_all [ind i]

private theorem iunfoldr.eq_test
    {f : Fin w → α → α × Bool} (state : Nat → α) (value : BitVec w) (a : α)
    (init : state 0 = a)
    (step : ∀(i : Fin w), f i (state i.val) = (state (i.val+1), value.getLsbD i.val)) :
    iunfoldr f a = (state w, BitVec.truncate w value) := by
  apply Fin.hIterate_eq (fun i => ((state i, BitVec.truncate i value) : α × BitVec i))
  case init =>
    simp only [init, eq_nil]
  case step =>
    intro i
    simp_all [setWidth_succ]

theorem iunfoldr_getLsbD' {f : Fin w → α → α × Bool} (state : Nat → α)
    (ind : ∀(i : Fin w), (f i (state i.val)).fst = state (i.val+1)) :
  (∀ i : Fin w, getLsbD (iunfoldr f (state 0)).snd i.val = (f i (state i.val)).snd)
  ∧ (iunfoldr f (state 0)).fst = state w := by
  unfold iunfoldr
  simp
  apply Fin.hIterate_elim
        (fun j (p : α × BitVec j) => (hj : j ≤ w) →
         (∀ i : Fin j,  getLsbD p.snd i.val = (f ⟨i.val, Nat.lt_of_lt_of_le i.isLt hj⟩ (state i.val)).snd)
          ∧ p.fst = state j)
  case hj => simp
  case init =>
    intro
    apply And.intro
    · intro i
      have := Fin.pos i
      contradiction
    · rfl
  case step =>
    intro j ⟨s, v⟩ ih hj
    apply And.intro
    case left =>
      intro i
      simp only [getLsbD_cons]
      have hj2 : j.val ≤ w := by simp
      cases (Nat.lt_or_eq_of_le (Nat.lt_succ.mp i.isLt)) with
      | inl h3 => simp [if_neg, (Nat.ne_of_lt h3)]
                  exact (ih hj2).1 ⟨i.val, h3⟩
      | inr h3 => simp [h3, if_pos]
                  cases (Nat.eq_zero_or_pos j.val) with
                  | inl hj3 => congr
                               rw [← (ih hj2).2]
                  | inr hj3 => congr
                               exact (ih hj2).2
    case right =>
      simp
      have hj2 : j.val ≤ w := by simp
      rw [← ind j, ← (ih hj2).2]


theorem iunfoldr_getLsbD {f : Fin w → α → α × Bool} (state : Nat → α) (i : Fin w)
    (ind : ∀(i : Fin w), (f i (state i.val)).fst = state (i.val+1)) :
  getLsbD (iunfoldr f (state 0)).snd i.val = (f i (state i.val)).snd := by
  exact (iunfoldr_getLsbD' state ind).1 i

/--
Correctness theorem for `iunfoldr`.
-/
theorem iunfoldr_replace
    {f : Fin w → α → α × Bool} (state : Nat → α) (value : BitVec w) (a : α)
    (init : state 0 = a)
    (step : ∀(i : Fin w), f i (state i.val) = (state (i.val+1), value.getLsbD i.val)) :
    iunfoldr f a = (state w, value) := by
  simp [iunfoldr.eq_test state value a init step]

theorem iunfoldr_replace_snd
  {f : Fin w → α → α × Bool} (state : Nat → α) (value : BitVec w) (a : α)
    (init : state 0 = a)
    (step : ∀(i : Fin w), f i (state i.val) = (state (i.val+1), value.getLsbD i.val)) :
    (iunfoldr f a).snd = value := by
  simp [iunfoldr.eq_test state value a init step]

end BitVec
