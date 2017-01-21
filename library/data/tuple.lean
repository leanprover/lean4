/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

Tuples are lists of a fixed size.
It is implemented as a subtype.
-/
import data.list

universe variables u v w

def tuple (α : Type u) (n : ℕ) := { l : list α // l^.length = n }

namespace tuple
variables {α : Type u} {β : Type v} {φ : Type w}
variable {n : ℕ}

instance [decidable_eq α] : decidable_eq (tuple α n) :=
begin unfold tuple, apply_instance end

@[pattern] def nil : tuple α 0 := ⟨[],  rfl⟩

@[pattern] def cons : α → tuple α n → tuple α (nat.succ n)
| a ⟨ v, h ⟩ := ⟨ a::v, congr_arg nat.succ h ⟩

@[reducible] def length (v : tuple α n) : ℕ := n

notation a :: b := cons a b
notation `[` l:(foldr `, ` (h t, cons h t) nil `]`) := l

open nat

def head : tuple α (nat.succ n) → α
| ⟨ [],     h ⟩ := by contradiction
| ⟨ a :: v, h ⟩ := a

theorem head_cons (a : α) : Π (v : tuple α n), head (a :: v) = a
| ⟨ l, h ⟩ := rfl

def tail : tuple α (succ n) → tuple α n
| ⟨ [],     h ⟩ := by contradiction
| ⟨ a :: v, h ⟩ := ⟨ v, congr_arg pred h ⟩

theorem tail_cons (a : α) : Π (v : tuple α n), tail (a :: v) = v
| ⟨ l, h ⟩ := rfl

def to_list : tuple α n → list α | ⟨ l, h ⟩ := l

def append {n m : nat} : tuple α n → tuple α m → tuple α (n + m)
| ⟨ l₁, h₁ ⟩ ⟨ l₂, h₂ ⟩ := ⟨ l₁ ++ l₂, by simp_using_hs ⟩

/- map -/

def map (f : α → β) : tuple α n → tuple β n
| ⟨ l, h ⟩  := ⟨ list.map f l, by simp_using_hs ⟩

@[simp] lemma map_nil (f : α → β) : map f nil = nil := rfl

lemma map_cons (f : α → β) (a : α) : Π (v : tuple α n), map f (a::v) = f a :: map f v
| ⟨l,h⟩ := rfl

def map₂ (f : α → β → φ) : tuple α n → tuple β n → tuple φ n
| ⟨ x, _ ⟩ ⟨ y, _ ⟩ := ⟨ list.map₂ f x y, by simp_using_hs ⟩

def repeat (a : α) (n : ℕ) : tuple α n :=
⟨ list.repeat a n, list.length_repeat a n ⟩

def dropn (i : ℕ) : tuple α n → tuple α (n - i)
| ⟨l, p⟩ := ⟨ list.dropn i l, by simp_using_hs ⟩

def firstn (i : ℕ) : tuple α n → tuple α (min i n)
| ⟨l, p⟩ := ⟨ list.firstn i l, by simp_using_hs ⟩

section accum
  open prod
  variable {σ : Type}

  def map_accumr (f : α → σ → σ × β) : tuple α n → σ → σ × tuple β n
  | ⟨ x, px ⟩ c :=
    let res := list.map_accumr f x c in
    ⟨ res.1, res.2, by simp_using_hs ⟩

  def map_accumr₂ {α β σ φ : Type} (f : α → β → σ → σ × φ)
   : tuple α n → tuple β n → σ → σ × tuple φ n
  | ⟨ x, px ⟩ ⟨ y, py ⟩ c :=
    let res := list.map_accumr₂ f x y c in
    ⟨ res.1, res.2, by simp_using_hs ⟩

end accum
end tuple
