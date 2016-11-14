/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

This is a minimal port of functions from the lean2 list library.
-/

import init.list
import algebra.order
import data.nat

universe variables u v w

namespace list

open nat

variables {A : Type u} { B : Type v } { C : Type w }

/- length theorems -/

theorem length_append : ∀ (x y : list A), length (x ++ y) = length x + length y
  | [] l := eq.symm (nat.zero_add (length l))
  | (a::s) l :=
     calc nat.succ (length (s ++ l))
            = nat.succ (length s + length l) : congr_arg nat.succ (length_append s l)
        ... = nat.succ (length s) + length l : eq.symm (nat.succ_add (length s) (length l))

theorem length_repeat (a : A) : ∀ (n : ℕ), length (repeat a n) = n
  | 0 := eq.refl 0
  | (succ i) := congr_arg succ (length_repeat i)

theorem length_map (f : A → B) : ∀ (a : list A), length (map f a) = length a
| [] := rfl
| (a :: l) := congr_arg succ (length_map l)

theorem length_dropn
: ∀ (i : ℕ) (l : list A), length (dropn i l) = length l - i
| 0 l := rfl
| (succ i) [] := eq.symm (nat.zero_sub_eq_zero (succ i))
| (succ i) (x::l) := calc
  length (dropn (succ i) (x::l))
          = length l - i             : length_dropn i l
      ... = succ (length l) - succ i : nat.sub_eq_succ_sub_succ (length l) i

/- firstn -/

def firstn : ℕ → list A → list A
| 0 l             := []
| (succ n) []     := []
| (succ n) (a::l) := a :: firstn n l

theorem length_firstn
: ∀ (i : ℕ) (l : list A), length (firstn i l) = min i (length l)
| 0        l      := eq.symm (nat.min_zero_left (length l))
| (succ n) []     := eq.symm (nat.min_zero_right (succ n))
| (succ n) (a::l) :=
  calc succ (length (firstn n l)) = succ (min n (length l)) : congr_arg succ (length_firstn n l)
                              ... = min (succ n) (succ (length l))
                                     : eq.symm (nat.min_succ_succ  n (length l))

/- map₂ -/

definition map₂ {A : Type u} {B : Type v} {C : Type w} (f : A → B → C) : list A → list B → list C
| [] l := []
| l [] := []
| (a::s) (b::t) := f a b :: map₂ s t

theorem map₂_nil_1 {A : Type u} {B : Type v} {C : Type w} (f : A → B → C)
   : Π y, map₂ f nil y = nil
| [] := eq.refl nil
| (b::t) := eq.refl nil

theorem map₂_nil_2 {A B C : Type} (f : A → B → C)
   : Π (x : list A), map₂ f x nil = nil
| [] := eq.refl nil
| (b::t) := eq.refl nil

theorem length_map₂ {A B C : Type} (f : A → B → C)
  : Π x y, length (map₂ f x y) = min (length x) (length y)
| [] y :=
   calc length (map₂ f nil y) = 0 : congr_arg length (map₂_nil_1 f y)
           ... = min 0 (length y) : eq.symm (nat.min_zero_left (length y))
| x [] :=
   calc length (map₂ f x nil) = 0 : congr_arg length (map₂_nil_2 f x)
           ... = min (length x) 0 : eq.symm (nat.min_zero_right (length x))
| (a::x) (b::y) :=
   calc succ (length (map₂ f x y))
             = succ (min (length x) (length y))
               : congr_arg succ (length_map₂ x y)
         ... = min (succ (length x)) (succ (length y))
               : eq.symm (min_succ_succ (length x) (length y))

section mapAccumR
variable {S : Type}

-- This runs a function over a list returning the intermediate results and a
-- a final result.
definition mapAccumR (f : A → S → S × B) : list A → S → (S × list B)
| [] c := (c, [])
| (y::yr) c :=
  let r := mapAccumR yr c in
  let z := f y (prod.fst r) in
  (prod.fst z, prod.snd z :: prod.snd r)

theorem length_mapAccumR
: ∀ (f : A → S → S × B) (x : list A) (s : S),
  length (prod.snd (mapAccumR f x s)) = length x
| f (a::x) s := congr_arg succ (length_mapAccumR f x s)
| f [] s := rfl

end mapAccumR

section mapAccumR₂

-- This runs a function over two lists returning the intermediate results and a
-- a final result.
definition mapAccumR₂ { A B S C : Type} (f : A → B → S → S × C)
  : list A → list B → S → S × list C
| [] _ c := (c,[])
| _ [] c := (c,[])
| (x::xr) (y::yr) c :=
  let r := mapAccumR₂ xr yr c in
  let q := f x y (prod.fst r) in
  (prod.fst q, prod.snd q :: (prod.snd r))

theorem length_mapAccumR₂ {A B S C : Type }
: ∀ (f : A → B → S → S × C) x y c,
  length (prod.snd (mapAccumR₂ f x y c)) = min (length x) (length y)
| f (a::x) (b::y) c := calc
    succ (length (prod.snd (mapAccumR₂ f x y c)))
              = succ (min (length x) (length y))
              : congr_arg succ (length_mapAccumR₂ f x y c)
          ... = min (succ (length x)) (succ (length y))
              : eq.symm (min_succ_succ (length x) (length y))
| f (a::x) [] c := rfl
| f [] (b::y) c := rfl
| f [] []     c := rfl
end mapAccumR₂

end list
