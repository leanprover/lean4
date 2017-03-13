/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.logic init.data.nat.basic
open decidable list

universes u v w

instance (α : Type u) : inhabited (list α) :=
⟨list.nil⟩

variables {α : Type u} {β : Type v} {γ : Type w}

namespace list
protected def append : list α → list α → list α
| []       l := l
| (h :: s) t := h :: (append s t)

instance : has_append (list α) :=
⟨list.append⟩

protected def mem : α → list α → Prop
| a []       := false
| a (b :: l) := a = b ∨ mem a l

instance : has_mem α (list α) :=
⟨list.mem⟩

instance decidable_mem [decidable_eq α] (a : α) : ∀ (l : list α), decidable (a ∈ l)
| []     := is_false not_false
| (b::l) :=
  if h₁ : a = b then is_true (or.inl h₁)
  else match decidable_mem l with
  | is_true  h₂ := is_true (or.inr h₂)
  | is_false h₂ := is_false (not_or h₁ h₂)
  end

def concat : list α → α → list α
| []     a := [a]
| (b::l) a := b :: concat l a

instance : has_emptyc (list α) :=
⟨list.nil⟩

protected def insert [decidable_eq α] (a : α) (l : list α) : list α :=
if a ∈ l then l else concat l a

instance [decidable_eq α] : has_insert α (list α) :=
⟨list.insert⟩

protected def union [decidable_eq α] : list α → list α → list α
| l₁ []      := l₁
| l₁ (a::l₂) := union (insert a l₁) l₂

instance [decidable_eq α] : has_union (list α) :=
⟨list.union⟩

protected def inter [decidable_eq α] : list α → list α → list α
| []      l₂ := []
| (a::l₁) l₂ := if a ∈ l₂ then a :: inter l₁ l₂ else inter l₁ l₂

instance [decidable_eq α] : has_inter (list α) :=
⟨list.inter⟩

def length : list α → nat
| []       := 0
| (a :: l) := length l + 1

def empty : list α → bool
| []       := tt
| (_ :: _) := ff

open option nat

def nth : list α → nat → option α
| []       n     := none
| (a :: l) 0     := some a
| (a :: l) (n+1) := nth l n

def update_nth : list α → ℕ → α → list α
| (x::xs) 0     a := a :: xs
| (x::xs) (i+1) a := x :: update_nth xs i a
| []      _     _ := []

def remove_nth : list α → ℕ → list α
| []      _     := []
| (x::xs) 0     := xs
| (x::xs) (i+1) := x :: remove_nth xs i

def remove_all [decidable_eq α] : list α → list α → list α
| (x :: xs) ys := (if x ∈ ys then remove_all xs ys else x :: remove_all xs ys)
| [] ys := []

def head [inhabited α] : list α → α
| []       := default α
| (a :: l) := a

def tail : list α → list α
| []       := []
| (a :: l) := l

def reverse_core : list α → list α → list α
| []     r := r
| (a::l) r := reverse_core l (a::r)

def reverse : list α → list α :=
λ l, reverse_core l []

def map (f : α → β) : list α → list β
| []       := []
| (a :: l) := f a :: map l

def for : list α → (α → β) → list β :=
flip map

def map₂ (f : α → β → γ) : list α → list β → list γ
| []      _       := []
| _       []      := []
| (x::xs) (y::ys) := f x y :: map₂ xs ys

def join : list (list α) → list α
| []        := []
| (l :: ls) := append l (join ls)

def filter (p : α → Prop) [decidable_pred p] : list α → list α
| []     := []
| (a::l) := if p a then a :: filter l else filter l

def find [decidable_eq α] : α → list α → nat
| a []       := 0
| a (b :: l) := if a = b then 0 else succ (find a l)

def dropn : ℕ → list α → list α
| 0 a := a
| (succ n) [] := []
| (succ n) (x::r) := dropn n r

def taken : ℕ → list α → list α
| 0 a := []
| (succ n) [] := []
| (succ n) (x :: r) := x :: taken n r

def foldl (f : α → β → α) : α → list β → α
| a []       := a
| a (b :: l) := foldl (f a b) l

def foldr (f : α → β → β) : β → list α → β
| b []       := b
| b (a :: l) := f a (foldr b l)

def any (l : list α) (p : α → bool) : bool :=
foldr (λ a r, p a || r) ff l

def all (l : list α) (p : α → bool) : bool :=
foldr (λ a r, p a && r) tt l

def bor  (l : list bool) : bool := any l id

def band (l : list bool) : bool := all l id

def zip_with (f : α → β → γ) : list α → list β → list γ
| (x::xs) (y::ys) := f x y :: zip_with xs ys
| _       _       := []

def zip : list α → list β → list (prod α β) :=
zip_with prod.mk

def unzip : list (α × β) → list α × list β
| []            := ([], [])
| ((a, b) :: t) := match unzip t with (al, bl) := (a::al, b::bl) end

def repeat (a : α) : ℕ → list α
| 0 := []
| (succ n) := a :: repeat n

def range_core : ℕ → list ℕ → list ℕ
| 0        l := l
| (succ n) l := range_core n (n :: l)

def range (n : ℕ) : list ℕ :=
range_core n []

def iota_core : ℕ → list ℕ → list ℕ
| 0        l := reverse l
| (succ n) l := iota_core n (succ n :: l)

def iota : ℕ → list ℕ :=
λ n, iota_core n []

def enum_from : ℕ → list α → list (ℕ × α)
| n [] := nil
| n (x :: xs) := (n, x) :: enum_from (n + 1) xs

def enum : list α → list (ℕ × α) := enum_from 0

def sum [has_add α] [has_zero α] : list α → α :=
foldl add zero

def last : Π l : list α, l ≠ [] → α
| []        h := absurd rfl h
| [a]       h := a
| (a::b::l) h := last (b::l) (λ h, list.no_confusion h)

def ilast [inhabited α] : list α → α
| []        := arbitrary α
| [a]       := a
| [a, b]    := b
| (a::b::l) := ilast l

def intersperse (sep : α) : list α → list α
| []      := []
| [x]     := [x]
| (x::xs) := x::sep::intersperse xs

def intercalate (sep : list α) (xs : list (list α)) : list α :=
join (intersperse sep xs)

@[inline] def bind {α : Type u} {β : Type v} (a : list α) (b : α → list β) : list β :=
join (map b a)

@[inline] def ret {α : Type u} (a : α) : list α :=
[a]
end list
