/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.logic init.data.nat.basic init.data.bool.basic init.propext
open decidable list

universes u v w

instance (α : Type u) : inhabited (list α) :=
⟨list.nil⟩

variables {α : Type u} {β : Type v} {γ : Type w}

namespace list

protected def has_dec_eq [s : decidable_eq α] : decidable_eq (list α)
| []      []      := is_true rfl
| (a::as) []      := is_false (λ h, list.no_confusion h)
| []      (b::bs) := is_false (λ h, list.no_confusion h)
| (a::as) (b::bs) :=
  match s a b with
  | is_true hab  :=
    match has_dec_eq as bs with
    | is_true habs  := is_true (eq.subst hab (eq.subst habs rfl))
    | is_false nabs := is_false (λ h, list.no_confusion h (λ _ habs, absurd habs nabs))
    end
  | is_false nab := is_false (λ h, list.no_confusion h (λ hab _, absurd hab nab))
  end

instance [decidable_eq α] : decidable_eq (list α) :=
list.has_dec_eq

@[simp] protected def append : list α → list α → list α
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

instance : has_emptyc (list α) :=
⟨list.nil⟩

protected def erase {α} [decidable_eq α] : list α → α → list α
| []     b := []
| (a::l) b := if a = b then l else a :: erase l b

protected def bag_inter {α} [decidable_eq α] : list α → list α → list α
| []      _   := []
| _       []  := []
| (a::l₁) l₂  := if a ∈ l₂ then a :: bag_inter l₁ (l₂.erase a) else bag_inter l₁ l₂

protected def diff {α} [decidable_eq α] : list α → list α → list α
| l      []      := l
| l₁     (a::l₂) := if a ∈ l₁ then diff (l₁.erase a) l₂ else diff l₁ l₂

@[simp] def length : list α → nat
| []       := 0
| (a :: l) := length l + 1

def empty : list α → bool
| []       := tt
| (_ :: _) := ff

open option nat

@[simp] def nth : list α → nat → option α
| []       n     := none
| (a :: l) 0     := some a
| (a :: l) (n+1) := nth l n

@[simp] def nth_le : Π (l : list α) (n), n < l.length → α
| []       n     h := absurd h (not_lt_zero n)
| (a :: l) 0     h := a
| (a :: l) (n+1) h := nth_le l n (le_of_succ_le_succ h)

@[simp] def head [inhabited α] : list α → α
| []       := default α
| (a :: l) := a

@[simp] def tail : list α → list α
| []       := []
| (a :: l) := l

def reverse_core : list α → list α → list α
| []     r := r
| (a::l) r := reverse_core l (a::r)

def reverse : list α → list α :=
λ l, reverse_core l []

@[simp] def map (f : α → β) : list α → list β
| []       := []
| (a :: l) := f a :: map l

@[simp] def map₂ (f : α → β → γ) : list α → list β → list γ
| []      _       := []
| _       []      := []
| (x::xs) (y::ys) := f x y :: map₂ xs ys

def join : list (list α) → list α
| []        := []
| (l :: ls) := l ++ join ls

def filter_map (f : α → option β) : list α → list β
| []     := []
| (a::l) :=
  match f a with
  | none   := filter_map l
  | some b := b :: filter_map l
  end

def filter (p : α → Prop) [decidable_pred p] : list α → list α
| []     := []
| (a::l) := if p a then a :: filter l else filter l

def partition (p : α → Prop) [decidable_pred p] : list α → list α × list α
| []     := ([], [])
| (a::l) := let (l₁, l₂) := partition l in if p a then (a :: l₁, l₂) else (l₁, a :: l₂)

def drop_while (p : α → Prop) [decidable_pred p] : list α → list α
| []     := []
| (a::l) := if p a then drop_while l else a::l

def span (p : α → Prop) [decidable_pred p] : list α → list α × list α
| []      := ([], [])
| (a::xs) := if p a then let (l, r) := span xs in (a :: l, r) else ([], a::xs)

def find_index (p : α → Prop) [decidable_pred p] : list α → nat
| []     := 0
| (a::l) := if p a then 0 else succ (find_index l)

def index_of [decidable_eq α] (a : α) : list α → nat := find_index (eq a)

def remove_all [decidable_eq α] (xs ys : list α) : list α :=
filter (∉ ys) xs

def update_nth : list α → ℕ → α → list α
| (x::xs) 0     a := a :: xs
| (x::xs) (i+1) a := x :: update_nth xs i a
| []      _     _ := []

def remove_nth : list α → ℕ → list α
| []      _     := []
| (x::xs) 0     := xs
| (x::xs) (i+1) := x :: remove_nth xs i

@[simp] def drop : ℕ → list α → list α
| 0        a      := a
| (succ n) []     := []
| (succ n) (x::r) := drop n r

@[simp] def take : ℕ → list α → list α
| 0        a        := []
| (succ n) []       := []
| (succ n) (x :: r) := x :: take n r

@[simp] def foldl (f : α → β → α) : α → list β → α
| a []       := a
| a (b :: l) := foldl (f a b) l

@[simp] def foldr (f : α → β → β) (b : β) : list α → β
| []       := b
| (a :: l) := f a (foldr l)

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

protected def insert [decidable_eq α] (a : α) (l : list α) : list α :=
if a ∈ l then l else a :: l

instance [decidable_eq α] : has_insert α (list α) :=
⟨list.insert⟩

protected def union [decidable_eq α] (l₁ l₂ : list α) : list α :=
foldr insert l₂ l₁

instance [decidable_eq α] : has_union (list α) :=
⟨list.union⟩

protected def inter [decidable_eq α] (l₁ l₂ : list α) : list α :=
filter (∈ l₂) l₁

instance [decidable_eq α] : has_inter (list α) :=
⟨list.inter⟩

@[simp] def repeat (a : α) : ℕ → list α
| 0 := []
| (succ n) := a :: repeat n

def range_core : ℕ → list ℕ → list ℕ
| 0        l := l
| (succ n) l := range_core n (n :: l)

def range (n : ℕ) : list ℕ :=
range_core n []

def iota : ℕ → list ℕ
| 0        := []
| (succ n) := succ n :: iota n

def enum_from : ℕ → list α → list (ℕ × α)
| n [] := nil
| n (x :: xs) := (n, x) :: enum_from (n + 1) xs

def enum : list α → list (ℕ × α) := enum_from 0

@[simp] def last : Π l : list α, l ≠ [] → α
| []        h := absurd rfl h
| [a]       h := a
| (a::b::l) h := last (b::l) (λ h, list.no_confusion h)

def ilast [inhabited α] : list α → α
| []        := arbitrary α
| [a]       := a
| [a, b]    := b
| (a::b::l) := ilast l

def init : list α → list α
| []     := []
| [a]    := []
| (a::l) := a::init l

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

protected def lt [has_lt α] : list α → list α → Prop
| []      []      := false
| []      (b::bs) := true
| (a::as) []      := false
| (a::as) (b::bs) := a < b ∨ lt as bs

instance [has_lt α] : has_lt (list α) :=
⟨list.lt⟩

instance has_decidable_lt [has_lt α] [h : decidable_rel ((<) : α → α → Prop)] : Π l₁ l₂ : list α, decidable (l₁ < l₂)
| []      []      := is_false not_false
| []      (b::bs) := is_true trivial
| (a::as) []      := is_false not_false
| (a::as) (b::bs) :=
  match h a b with
  | is_true h₁  := is_true (or.inl h₁)
  | is_false h₁ :=
    match has_decidable_lt as bs with
    | is_true h₂  := is_true (or.inr h₂)
    | is_false h₂ := is_false (λ hd, or.elim hd (λ n₁, absurd n₁ h₁) (λ n₂, absurd n₂ h₂))
    end
  end

@[reducible] protected def le [has_lt α] (a b : list α) : Prop :=
¬ b < a

instance [has_lt α] : has_le (list α) :=
⟨list.le⟩

instance has_decidable_le [has_lt α] [h : decidable_rel ((<) : α → α → Prop)] : Π l₁ l₂ : list α, decidable (l₁ ≤ l₂) :=
λ a b, not.decidable

lemma le_eq_not_gt [has_lt α] : ∀ l₁ l₂ : list α, (l₁ ≤ l₂) = ¬ (l₂ < l₁) :=
λ l₁ l₂, rfl

lemma lt_eq_not_ge [has_lt α] [decidable_rel ((<) : α → α → Prop)] : ∀ l₁ l₂ : list α, (l₁ < l₂) = ¬ (l₂ ≤ l₁) :=
λ l₁ l₂,
  show (l₁ < l₂) = ¬ ¬ (l₁ < l₂), from
  eq.subst (propext (not_not_iff (l₁ < l₂))).symm rfl

end list

namespace bin_tree
private def to_list_aux : bin_tree α → list α → list α
| empty      as := as
| (leaf a)   as := a::as
| (node l r) as := to_list_aux l (to_list_aux r as)

def to_list (t : bin_tree α) : list α :=
to_list_aux t []
end bin_tree
