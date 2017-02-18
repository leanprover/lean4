/-
Copyright (c) 2015 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Haitao Zhang, Floris van Doorn

List combinators.
-/
import init.data.list.basic

universes u v w

namespace list

open nat

variables {α : Type u} {β : Type v} {φ : Type w}

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

@[simp]
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

@[simp]
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
