/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.logic init.nat
open decidable list

notation h :: t  := cons h t
notation `[` l:(foldr `, ` (h t, cons h t) nil `]`) := l

universe variables u v

instance (A : Type u) : inhabited (list A) :=
⟨list.nil⟩

variables {A : Type u} {B : Type v}

namespace list
protected def append : list A → list A → list A
| []       l := l
| (h :: s) t := h :: (append s t)

instance : has_append (list A) :=
⟨list.append⟩

protected def mem : A → list A → Prop
| a []       := false
| a (b :: l) := a = b ∨ mem a l

instance : has_mem A list :=
⟨list.mem⟩

instance decidable_mem [decidable_eq A] (a : A) : ∀ (l : list A), decidable (a ∈ l)
| []     := is_false not_false
| (b::l) :=
  if h₁ : a = b then is_true (or.inl h₁)
  else match decidable_mem l with
  | is_true  h₂ := is_true (or.inr h₂)
  | is_false h₂ := is_false (not_or h₁ h₂)
  end

def concat : list A → A → list A
| []     a := [a]
| (b::l) a := b :: concat l a

instance : has_emptyc (list A) :=
⟨list.nil⟩

protected def insert [decidable_eq A] (a : A) (l : list A) : list A :=
if a ∈ l then l else concat l a

instance [decidable_eq A] : has_insert A list :=
⟨list.insert⟩

protected def union [decidable_eq A] : list A → list A → list A
| l₁ []      := l₁
| l₁ (a::l₂) := union (insert a l₁) l₂

instance [decidable_eq A] : has_union (list A) :=
⟨list.union⟩

protected def inter [decidable_eq A] : list A → list A → list A
| []      l₂ := []
| (a::l₁) l₂ := if a ∈ l₂ then a :: inter l₁ l₂ else inter l₁ l₂

instance [decidable_eq A] : has_inter (list A) :=
⟨list.inter⟩

def length : list A → nat
| []       := 0
| (a :: l) := length l + 1

open option nat

def nth : list A → nat → option A
| []       n     := none
| (a :: l) 0     := some a
| (a :: l) (n+1) := nth l n

def head [inhabited A] : list A → A
| []       := default A
| (a :: l) := a

def tail : list A → list A
| []       := []
| (a :: l) := l

def reverse : list A → list A
| []       := []
| (a :: l) := concat (reverse l) a

def map (f : A → B) : list A → list B
| []       := []
| (a :: l) := f a :: map l

def for : list A → (A → B) → list B :=
flip map

def join : list (list A) → list A
| []        := []
| (l :: ls) := append l (join ls)

def filter (p : A → Prop) [h : decidable_pred p] : list A → list A
| []     := []
| (a::l) := if p a then a :: filter l else filter l

def dropn : ℕ → list A → list A
| 0 a := a
| (succ n) [] := []
| (succ n) (x::r) := dropn n r

definition foldl (f : A → B → A) : A → list B → A
| a []       := a
| a (b :: l) := foldl (f a b) l

definition foldr (f : A → B → B) : B → list A → B
| b []       := b
| b (a :: l) := f a (foldr b l)

definition any (l : list A) (p : A → bool) : bool :=
foldr (λ a r, p a || r) ff l

definition all (l : list A) (p : A → bool) : bool :=
foldr (λ a r, p a && r) tt l

def zip : list A → list B → list (prod A B)
| []      _       := []
| _       []      := []
| (x::xs) (y::ys) := (prod.mk x y) :: zip xs ys

def repeat (a : A) : ℕ → list A
| 0 := []
| (succ n) := a :: repeat n

def iota : ℕ → list ℕ
| 0 := []
| (succ n) := iota n ++ [succ n]

end list
