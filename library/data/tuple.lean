/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

Tuples are lists of a fixed size.
It is implemented as a subtype.
-/
import data.list
import init.subtype

def tuple (A : Type) (n : ℕ) := {l : list A // list.length l = n}

namespace tuple
  variables {A B C : Type}
  variable {n : ℕ}

  definition nil : tuple A 0 := ⟨ [],  rfl ⟩

  definition cons : A → tuple A n → tuple A (nat.succ n)
  | a ⟨ v, h ⟩ := ⟨ a::v, congr_arg nat.succ h ⟩

  notation a :: b := cons a b
  notation `[` l:(foldr `, ` (h t, cons h t) nil `]`) := l

  open nat

  definition head : tuple A (nat.succ n) → A
  | ⟨list.nil,      h ⟩ := let q : 0 = succ n := h in by contradiction
  | ⟨list.cons a v, h ⟩ := a

  theorem head_cons (a : A) : Π (v : tuple A n), head (a :: v) = a
  | ⟨ l, h ⟩ := rfl

  definition tail : tuple A (succ n) → tuple A n
  | ⟨ list.nil,   h ⟩ := let q : 0 = succ n := h in by contradiction
  | ⟨ list.cons a v, h ⟩ := ⟨ v,  congr_arg pred h ⟩

  theorem tail_cons (a : A) : Π (v : tuple A n), tail (a :: v) = v
  | ⟨ l, h ⟩ := rfl

  definition to_list : tuple A n → list A | ⟨ l, h ⟩ := l

  /- append -/

  definition append {n m : nat} : tuple A n → tuple A m → tuple A (n + m)
  | ⟨ l₁, h₁ ⟩ ⟨ l₂, h₂ ⟩ :=
    let p := calc
       list.length (l₁ ++ l₂)
             = list.length l₁ + list.length l₂ : list.length_append l₁ l₂
         ... = n + list.length l₂ : congr_arg (λi, i + list.length l₂) h₁
         ... = n + m              : congr_arg (λi, n + i) h₂ in
    ⟨ list.append l₁ l₂, p ⟩

  /- map -/

  definition map (f : A → B) : tuple A n → tuple B n
  | ⟨ l, h ⟩  :=
    let q := calc list.length (list.map f l) = list.length l : list.length_map f l
                                         ... = n             : h in
    ⟨ list.map f l, q ⟩

  theorem map_nil (f : A → B) : map f nil = nil := rfl

  theorem map_cons (f : A → B) (a : A)
        : Π (v : tuple A n), map f (a::v) = f a :: map f v
  | ⟨ l, h ⟩ := rfl

  definition map₂ (f : A → B → C) : tuple A n → tuple B n → tuple C n
  | ⟨ x, px ⟩ ⟨ y, py ⟩ :=
    let z : list C := list.map₂ f x y in
    let pxx : list.length x = n := px in
    let pyy : list.length y = n := py in
    let p : list.length z = n := calc
         list.length z = min (list.length x) (list.length y) : list.length_map₂ f x y
                   ... = min n n                             : by rewrite [pxx, pyy]
                   ... = n                                   : min_self n in
    ⟨ z, p ⟩

  definition repeat (a : A) : tuple A n
    := ⟨ list.repeat a n, list.length_repeat a n ⟩

  definition dropn : Π (i:ℕ), tuple A n → tuple A (n - i)
  | i ⟨ l, p ⟩ := ⟨ list.dropn i l, p ▸ list.length_dropn i l ⟩

  definition firstn : Π (i:ℕ) {p:i ≤ n}, tuple A n → tuple A i
  | i isLe ⟨ l, p ⟩ :=
    let q := calc list.length (list.firstn i l)
                     = min i (list.length l)  : list.length_firstn i l
                 ... = min i n                : congr_arg (λ v, min i v) p
                 ... = i                      : min_eq_left isLe in
    ⟨ list.firstn i l, q ⟩

  section accum
  open prod
  variable {S : Type}

  definition mapAccumR
  : (A → S → S × B) → tuple A n → S → S × tuple B n
  | f ⟨ x, px ⟩ c :=
    let z := list.mapAccumR f x c in
    let p := eq.trans (list.length_mapAccumR f x c) px in
    (prod.fst z, ⟨ prod.snd z, p ⟩)

  definition mapAccumR₂
  : (A → B → S → S × C) → tuple A n → tuple B n → S → S × tuple C n
  | f ⟨ x, px ⟩ ⟨ y, py ⟩ c :=
    let z := list.mapAccumR₂ f x y c in
    let pxx : list.length x = n := px in
    let pyy : list.length y = n := py in
    let p := calc
          list.length (prod.snd (list.mapAccumR₂ f x y c))
                  = min (list.length x) (list.length y)  : list.length_mapAccumR₂ f x y c
              ... = n                                    : by rewrite [ pxx, pyy, min_self ] in
    (prod.fst z, ⟨prod.snd z, p ⟩)

  end accum
end tuple
