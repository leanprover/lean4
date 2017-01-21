/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn

Basic properties of lists.
-/
import init.data.list.basic

universe variables u v w

namespace list

open nat

variables {α : Type u} {β : Type v} {φ : Type w}

/- length theorems -/

@[simp]
theorem length_append : ∀ (x y : list α), length (x ++ y) = length x + length y
  | [] l := eq.symm (nat.zero_add (length l))
  | (a::s) l :=
     calc succ (length (s ++ l))
            = succ (length s + length l) : congr_arg nat.succ (length_append s l)
        ... = succ (length s) + length l : eq.symm (nat.succ_add (length s) (length l))

theorem length_concat (a : α) : ∀ (l : list α), length (concat l a) = succ (length l)
  | nil := rfl
  | (cons b l) := congr_arg succ (length_concat l)

@[simp]
theorem length_dropn
: ∀ (i : ℕ) (l : list α), length (dropn i l) = length l - i
| 0 l := rfl
| (succ i) [] := eq.symm (nat.zero_sub_eq_zero (succ i))
| (succ i) (x::l) := calc
  length (dropn (succ i) (x::l))
          = length l - i             : length_dropn i l
      ... = succ (length l) - succ i : nat.sub_eq_succ_sub_succ (length l) i

@[simp]
theorem length_map (f : α → β) : ∀ (a : list α), length (map f a) = length a
| [] := rfl
| (a :: l) := congr_arg succ (length_map l)

@[simp]
theorem length_repeat (a : α) : ∀ (n : ℕ), length (repeat a n) = n
  | 0 := eq.refl 0
  | (succ i) := congr_arg succ (length_repeat i)

/- firstn -/

def firstn : ℕ → list α → list α
| 0 l             := []
| (succ n) []     := []
| (succ n) (a::l) := a :: firstn n l

@[simp]
theorem length_firstn
: ∀ (i : ℕ) (l : list α), length (firstn i l) = min i (length l)
| 0        l      := eq.symm (nat.zero_min (length l))
| (succ n) []     := eq.symm (nat.min_zero (succ n))
| (succ n) (a::l) :=
  calc succ (length (firstn n l)) = succ (min n (length l)) : congr_arg succ (length_firstn n l)
                              ... = min (succ n) (succ (length l))
                                     : eq.symm (nat.min_succ_succ  n (length l))

end list
