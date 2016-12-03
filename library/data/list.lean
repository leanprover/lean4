/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

This is a minimal port of functions from the lean2 list library.
-/
import init.data.list.basic

import data.nat.order

universe variables u v w

namespace list

open nat

variables {α : Type u} {β : Type v} {φ : Type w}

/- length theorems -/

theorem length_append : ∀ (x y : list α), length (x ++ y) = length x + length y
  | [] l := eq.symm (nat.zero_add (length l))
  | (a::s) l :=
     calc nat.succ (length (s ++ l))
            = nat.succ (length s + length l) : congr_arg nat.succ (length_append s l)
        ... = nat.succ (length s) + length l : eq.symm (nat.succ_add (length s) (length l))

theorem length_repeat (a : α) : ∀ (n : ℕ), length (repeat a n) = n
  | 0 := eq.refl 0
  | (succ i) := congr_arg succ (length_repeat i)

theorem length_map (f : α → β) : ∀ (a : list α), length (map f a) = length a
| [] := rfl
| (a :: l) := congr_arg succ (length_map l)

theorem length_dropn
: ∀ (i : ℕ) (l : list α), length (dropn i l) = length l - i
| 0 l := rfl
| (succ i) [] := eq.symm (nat.zero_sub_eq_zero (succ i))
| (succ i) (x::l) := calc
  length (dropn (succ i) (x::l))
          = length l - i             : length_dropn i l
      ... = succ (length l) - succ i : nat.sub_eq_succ_sub_succ (length l) i

definition has_decidable_eq [h : decidable_eq α]
: ∀ (x y : list α), decidable (x = y)
| nil nil := is_true rfl
| nil (cons b s) := is_false (λ q, list.no_confusion q)
| (cons a r) nil := is_false (λ q, list.no_confusion q)
| (cons a r) (cons b s) :=
  match h a b with
  | (is_true h₁) :=
    match has_decidable_eq r s with
    | (is_true  h₂) :=
       is_true (calc a :: r = b :: r : congr_arg (λc, c :: r) h₁
                        ... = b :: s : congr_arg (λt, b :: t) h₂)
    | (is_false h₂) :=
      is_false (λ q, list.no_confusion q (λ heq teq, h₂ teq))
    end
  | (is_false h₁) :=
     is_false (λ q, list.no_confusion q (λ heq teq, h₁ heq))
  end

/- firstn -/

def firstn : ℕ → list α → list α
| 0 l             := []
| (succ n) []     := []
| (succ n) (a::l) := a :: firstn n l

theorem length_firstn
: ∀ (i : ℕ) (l : list α), length (firstn i l) = min i (length l)
| 0        l      := eq.symm (nat.zero_min (length l))
| (succ n) []     := eq.symm (nat.min_zero (succ n))
| (succ n) (a::l) :=
  calc succ (length (firstn n l)) = succ (min n (length l)) : congr_arg succ (length_firstn n l)
                              ... = min (succ n) (succ (length l))
                                     : eq.symm (nat.min_succ_succ  n (length l))

/- map₂ -/

definition map₂ {α : Type u} {β : Type v} {φ : Type w} (f : α → β → φ) : list α → list β → list φ
| [] l := []
| l [] := []
| (a::s) (b::t) := f a b :: map₂ s t

theorem map₂_nil_1 {α : Type u} {β : Type v} {φ : Type w} (f : α → β → φ)
   : Π y, map₂ f nil y = nil
| [] := eq.refl nil
| (b::t) := eq.refl nil

theorem map₂_nil_2 {α : Type u} {β : Type v} {φ : Type w} (f : α → β → φ)
   : Π (x : list α), map₂ f x nil = nil
| [] := eq.refl nil
| (b::t) := eq.refl nil

theorem length_map₂ {α : Type u} {β : Type v} {φ : Type w} (f : α → β → φ)
  : Π x y, length (map₂ f x y) = min (length x) (length y)
| [] y :=
   calc length (map₂ f nil y) = 0 : congr_arg length (map₂_nil_1 f y)
           ... = min 0 (length y) : eq.symm (nat.zero_min (length y))
| x [] :=
   calc length (map₂ f x nil) = 0 : congr_arg length (map₂_nil_2 f x)
           ... = min (length x) 0 : eq.symm (nat.min_zero (length x))
| (a::x) (b::y) :=
   calc succ (length (map₂ f x y))
             = succ (min (length x) (length y))
               : congr_arg succ (length_map₂ x y)
         ... = min (succ (length x)) (succ (length y))
               : eq.symm (min_succ_succ (length x) (length y))

section map_accumr
variable {σ : Type}

-- This runs a function over a list returning the intermediate results and a
-- a final result.
definition map_accumr (f : α → σ → σ × β) : list α → σ → (σ × list β)
| [] c := (c, [])
| (y::yr) c :=
  let r := map_accumr yr c in
  let z := f y (prod.fst r) in
  (prod.fst z, prod.snd z :: prod.snd r)

theorem length_map_accumr
: ∀ (f : α → σ → σ × β) (x : list α) (s : σ),
  length (prod.snd (map_accumr f x s)) = length x
| f (a::x) s := congr_arg succ (length_map_accumr f x s)
| f [] s := rfl

end map_accumr

section map_accumr₂

-- This runs a function over two lists returning the intermediate results and a
-- a final result.
definition map_accumr₂ {α β σ φ : Type} (f : α → β → σ → σ × φ)
  : list α → list β → σ → σ × list φ
| [] _ c := (c,[])
| _ [] c := (c,[])
| (x::xr) (y::yr) c :=
  let r := map_accumr₂ xr yr c in
  let q := f x y (prod.fst r) in
  (prod.fst q, prod.snd q :: (prod.snd r))

theorem length_map_accumr₂ {α β σ φ : Type}
: ∀ (f : α → β → σ → σ × φ) x y c,
  length (prod.snd (map_accumr₂ f x y c)) = min (length x) (length y)
| f (a::x) (b::y) c := calc
    succ (length (prod.snd (map_accumr₂ f x y c)))
              = succ (min (length x) (length y))
              : congr_arg succ (length_map_accumr₂ f x y c)
          ... = min (succ (length x)) (succ (length y))
              : eq.symm (min_succ_succ (length x) (length y))
| f (a::x) [] c := rfl
| f [] (b::y) c := rfl
| f [] []     c := rfl
end map_accumr₂

end list
