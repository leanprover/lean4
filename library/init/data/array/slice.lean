/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
prelude
import init.data.nat init.data.array.basic init.data.nat.lemmas
universes u
variables {α : Type u} {n : nat}

namespace array

def slice (a : array α n) (k l : nat) (h₁ : k ≤ l) (h₂ : l ≤ n) : array α (l - k) :=
⟨ λ ⟨ i, hi ⟩, a.read ⟨ i + k,
  calc i + k < (l - k) + k : add_lt_add_right hi _
         ... = l : nat.sub_add_cancel h₁
         ... ≤ n : h₂⟩ ⟩

def taken (a : array α n) (m : nat) (h : m ≤ n) : array α m :=
cast (by simp) $ a.slice 0 m (nat.zero_le _) h

def dropn (a : array α n) (m : nat) (h : m ≤ n) : array α (n-m) :=
a.slice m n h (le_refl _)

private lemma sub_sub_cancel (m n : ℕ) (h : m ≤ n) : n - (n - m) = m :=
calc n - (n - m) = (n - m) + m - (n - m) : by rw nat.sub_add_cancel; assumption
             ... = m : nat.add_sub_cancel_left _ _

def taken_right (a : array α n) (m : nat) (h : m ≤ n) : array α m :=
cast (by simp [*, sub_sub_cancel]) $ a.dropn (n - m) (nat.sub_le _ _)

def reverse (a : array α n) : array α n :=
⟨ λ ⟨ i, hi ⟩, a.read ⟨ n - (i + 1),
  begin apply nat.sub_lt_of_pos_le, apply nat.zero_lt_succ, assumption end ⟩ ⟩

end array
