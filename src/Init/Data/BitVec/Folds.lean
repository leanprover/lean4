/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix
-/
prelude
import Init.Data.BitVec.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Fin.Iterate

namespace Std.BitVec

/--
iunfoldr is an iterative operation that applies a function `f` repeatedly.

It produces a sequence of state values `[s_0, s_1 .. s_w]` and a bitvector
`v` where `f i s_i = (s_{i+1}, b_i)` and `b_i` is bit `i`th least-significant bit
in `v` (e.g., `getLsb v i = b_i`).

Theorems involving `iunfoldr` can be eliminated using `iunfoldr_replace` below.
-/
def iunfoldr (f : Fin w → α → α × Bool) (s : α) : α × BitVec w :=
  Fin.hIterate (fun i => α × BitVec i) (s, nil) fun i q =>
    (fun p => ⟨p.fst, cons p.snd q.snd⟩) (f i q.fst)

theorem iunfoldr.fst_eq
    {f : Fin w → α → α × Bool} (state : Fin (w+1) → α) (s : α)
    (init : s = state 0)
    (ind : ∀(i : Fin w), (f i (state i.castSucc)).fst = state i.succ) :
    (iunfoldr f s).fst = state (Fin.last _) := by
  unfold iunfoldr
  apply Fin.hIterate_elim (P := (α × BitVec ·)) (Q := fun i p => p.fst = state i)
  case init =>
    exact init
  case step =>
    intro i ⟨s, v⟩ p
    simp_all [ind i]

private theorem iunfoldr.eq_test
    {f : Fin w → α → α × Bool} (state : Fin (w+1) → α) (value : BitVec w) (a : α)
    (init : state 0 = a)
    (step : ∀(i : Fin w), f i (state i.castSucc) = (state (i.succ), value.getLsb i.val)) :
    iunfoldr f a = (state (Fin.last _), BitVec.truncate w value) := by
  apply Fin.hIterate_eq (P := (α × BitVec ·))
    (fun i => ((state i, BitVec.truncate i value) : α × BitVec i))
  case init =>
    simp only [init, eq_nil]
  case step =>
    intro i
    simp_all [truncate_succ]

/--
Correctness theorem for `iunfoldr`.
-/
theorem iunfoldr_replace
    {f : Fin w → α → α × Bool} (state : Fin (w+1) → α) (value : BitVec w) (a : α)
    (init : state 0 = a)
    (step : ∀(i : Fin w), f i (state i.castSucc) = (state (i.succ), value.getLsb i.val)) :
    iunfoldr f a = (state (Fin.last _), value) := by
  simp [iunfoldr.eq_test state value a init step]

