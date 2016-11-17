/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

Tuples are lists of a fixed size.
It is implemented as a subtype.
-/
import data.list
import init.subtype

def tuple (α : Type) (n : ℕ) := {l : list α // list.length l = n}

namespace tuple
  variables {α β φ : Type}
  variable {n : ℕ}

  definition nil : tuple α 0 := ⟨ [],  rfl ⟩

  definition cons : α → tuple α n → tuple α (nat.succ n)
  | a ⟨ v, h ⟩ := ⟨ a::v, congr_arg nat.succ h ⟩

  notation a :: b := cons a b
  notation `[` l:(foldr `, ` (h t, cons h t) nil `]`) := l

  open nat

  definition head : tuple α (nat.succ n) → α
  | ⟨list.nil,      h ⟩ := let q : 0 = succ n := h in by contradiction
  | ⟨list.cons a v, h ⟩ := a

  theorem head_cons (a : α) : Π (v : tuple α n), head (a :: v) = a
  | ⟨ l, h ⟩ := rfl

  definition tail : tuple α (succ n) → tuple α n
  | ⟨ list.nil,   h ⟩ := let q : 0 = succ n := h in by contradiction
  | ⟨ list.cons a v, h ⟩ := ⟨ v,  congr_arg pred h ⟩

  theorem tail_cons (a : α) : Π (v : tuple α n), tail (a :: v) = v
  | ⟨ l, h ⟩ := rfl

  definition to_list : tuple α n → list α | ⟨ l, h ⟩ := l

  /- append -/

  definition append {n m : nat} : tuple α n → tuple α m → tuple α (n + m)
  | ⟨ l₁, h₁ ⟩ ⟨ l₂, h₂ ⟩ :=
    let p := calc
       list.length (l₁ ++ l₂)
             = list.length l₁ + list.length l₂ : list.length_append l₁ l₂
         ... = n + list.length l₂ : congr_arg (λi, i + list.length l₂) h₁
         ... = n + m              : congr_arg (λi, n + i) h₂ in
    ⟨ list.append l₁ l₂, p ⟩

  /- map -/

  definition map (f : α → β) : tuple α n → tuple β n
  | ⟨ l, h ⟩  :=
    let q := calc list.length (list.map f l) = list.length l : list.length_map f l
                                         ... = n             : h in
    ⟨ list.map f l, q ⟩

  theorem map_nil (f : α → β) : map f nil = nil := rfl

  theorem map_cons (f : α → β) (a : α)
        : Π (v : tuple α n), map f (a::v) = f a :: map f v
  | ⟨ l, h ⟩ := rfl

  definition map₂ (f : α → β → φ) : tuple α n → tuple β n → tuple φ n
  | ⟨ x, px ⟩ ⟨ y, py ⟩ :=
    let z : list φ := list.map₂ f x y in
    let pxx : list.length x = n := px in
    let pyy : list.length y = n := py in
    let p : list.length z = n := calc
         list.length z = min (list.length x) (list.length y) : list.length_map₂ f x y
                   ... = min n n                             : by rewrite [pxx, pyy]
                   ... = n                                   : min_self n in
    ⟨ z, p ⟩

  definition repeat (a : α) : tuple α n
    := ⟨ list.repeat a n, list.length_repeat a n ⟩

  definition dropn : Π (i:ℕ), tuple α n → tuple α (n - i)
  | i ⟨ l, p ⟩ := ⟨ list.dropn i l, p ▸ list.length_dropn i l ⟩

  definition firstn : Π (i:ℕ) {p:i ≤ n}, tuple α n → tuple α i
  | i is_le ⟨ l, p ⟩ :=
    let q := calc list.length (list.firstn i l)
                     = min i (list.length l)  : list.length_firstn i l
                 ... = min i n                : congr_arg (λ v, min i v) p
                 ... = i                      : min_eq_left is_le in
    ⟨ list.firstn i l, q ⟩

  section accum
  open prod
  variable {σ : Type}

  definition map_accumr
  : (α → σ → σ × β) → tuple α n → σ → σ × tuple β n
  | f ⟨ x, px ⟩ c :=
    let z := list.map_accumr f x c in
    let p := eq.trans (list.length_map_accumr f x c) px in
    (prod.fst z, ⟨ prod.snd z, p ⟩)

  definition map_accumr₂
  : (α → β → σ → σ × φ) → tuple α n → tuple β n → σ → σ × tuple φ n
  | f ⟨ x, px ⟩ ⟨ y, py ⟩ c :=
    let z := list.map_accumr₂ f x y c in
    let pxx : list.length x = n := px in
    let pyy : list.length y = n := py in
    let p := calc
          list.length (prod.snd (list.map_accumr₂ f x y c))
                  = min (list.length x) (list.length y)  : list.length_map_accumr₂ f x y c
              ... = n                                    : by rewrite [ pxx, pyy, min_self ] in
    (prod.fst z, ⟨prod.snd z, p ⟩)

  end accum
end tuple
