/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.core init.data.nat.basic
open decidable list

universes u v w

instance (α : Type u) : inhabited (list α) :=
⟨list.nil⟩

variables {α : Type u} {β : Type v} {γ : Type w}

namespace list

protected def has_dec_eq [decidable_eq α] : Π a b : list α, decidable (a = b)
| []      []      := is_true rfl
| (a::as) []      := is_false (λ h, list.no_confusion h)
| []      (b::bs) := is_false (λ h, list.no_confusion h)
| (a::as) (b::bs) :=
  match dec_eq a b with
  | is_true hab  :=
    (match has_dec_eq as bs with
     | is_true habs  := is_true (eq.subst hab (eq.subst habs rfl))
     | is_false nabs := is_false (λ h, list.no_confusion h (λ _ habs, absurd habs nabs)))
  | is_false nab := is_false (λ h, list.no_confusion h (λ hab _, absurd hab nab))

instance [decidable_eq α] : decidable_eq (list α) :=
{dec_eq := list.has_dec_eq}

def reverse_core : list α → list α → list α
| []     r := r
| (a::l) r := reverse_core l (a::r)

local infix `**`:66 := reverse_core

def reverse : list α → list α :=
λ l, reverse_core l []

protected def append (as bs : list α) : list α :=
reverse_core as.reverse bs

instance : has_append (list α) :=
⟨list.append⟩

theorem reverse_core_reverse_core_nil : ∀ (as bs : list α), (as ** bs) ** [] = bs ** as
| []  bs     := rfl
| (a::as) bs :=
  show reverse_core (reverse_core as (a::bs)) [] = reverse_core bs (a::as), from
  reverse_core_reverse_core_nil as (a::bs)

theorem nil_append (as : list α) : [] ++ as = as :=
rfl

theorem append_nil (as : list α) : as ++ [] = as :=
show (as ** []) ** [] = as, from
reverse_core_reverse_core_nil as []

theorem reverse_core_reverse_core : ∀ (as bs cs : list α), (as ** bs) ** cs = bs ** ((as ** []) ** cs)
| []      bs cs := rfl
| (a::as) bs cs :=
  show (as ** a::bs) ** cs = bs ** ((as ** [a]) ** cs), from
  have h₁ : (as ** a::bs) ** cs = bs ** a::((as ** []) ** cs),       from reverse_core_reverse_core as (a::bs) cs,
  have h₂ : ((as ** [a]) ** cs) = a::((as ** []) ** cs),             from reverse_core_reverse_core as [a] cs,
  have h₃ : bs ** a::((as ** []) ** cs) = bs ** ((as ** [a]) ** cs), from congr_arg (λ b, bs ** b) h₂.symm,
  eq.trans h₁ h₃

theorem cons_append (a : α) (as bs : list α) : (a::as) ++ bs = a::(as ++ bs) :=
reverse_core_reverse_core as [a] bs

theorem append_assoc : ∀ (as bs cs : list α), (as ++ bs) ++ cs = as ++ (bs ++ cs)
| []      bs cs := rfl
| (a::as) bs cs :=
  show ((a::as) ++ bs) ++ cs = (a::as) ++ (bs ++ cs),      from
  have h₁ : ((a::as) ++ bs) ++ cs = a::(as++bs) ++ cs,     from congr_arg (++ cs) (cons_append a as bs),
  have h₂ : a::(as++bs) ++ cs     = a::((as++bs) ++ cs),   from cons_append a (as++bs) cs,
  have h₃ : a::((as++bs) ++ cs)   = a::(as ++ (bs ++ cs)), from congr_arg (λ as, a::as) (append_assoc as bs cs),
  have h₄ : a::(as ++ (bs ++ cs)) = (a::as ++ (bs ++ cs)), from (cons_append a as (bs++cs)).symm,
  eq.trans (eq.trans (eq.trans h₁ h₂) h₃) h₄

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

def nth_le : Π (l : list α) (n), n < l.length → α
| []       n     h := absurd h (not_lt_zero n)
| (a :: l) 0     h := a
| (a :: l) (n+1) h := nth_le l n (le_of_succ_le_succ h)

def head [inhabited α] : list α → α
| []       := default α
| (a :: l) := a

def tail : list α → list α
| []       := []
| (a :: l) := l

@[specialize] def map (f : α → β) : list α → list β
| []       := []
| (a :: l) := f a :: map l

@[specialize] def map₂ (f : α → β → γ) : list α → list β → list γ
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

def index_of [decidable_eq α] (a : α) (l : list α) : nat :=
find_index (eq a) l

def assoc [decidable_eq α] : list (α × β) → α → option β
| []         _  := none
| ((a,b)::l) a' := if a = a' then some b else assoc l a'

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

def drop : ℕ → list α → list α
| 0        a      := a
| (succ n) []     := []
| (succ n) (x::r) := drop n r

def take : ℕ → list α → list α
| 0        a        := []
| (succ n) []       := []
| (succ n) (x :: r) := x :: take n r

@[specialize] def foldl (f : α → β → α) : α → list β → α
| a []       := a
| a (b :: l) := foldl (f a b) l

@[specialize] def foldr (f : α → β → β) (b : β) : list α → β
| []       := b
| (a :: l) := f a (foldr l)

@[specialize] def foldr1 (f : α → α → α) : Π (xs : list α), xs ≠ [] → α
| []              nem := false.elim (nem rfl)
| [a]             nem := a
| (a :: l@(_::_)) nem := f a (foldr1 l (λ eq, list.no_confusion eq))

@[specialize] def foldr1_opt (f : α → α → α) : list α → option α
| []       := none
| (a :: l) := some $ foldr1 f (a :: l) (λ eq, list.no_confusion eq)

@[inline] def any (l : list α) (p : α → bool) : bool :=
foldr (λ a r, p a || r) ff l

@[inline] def all (l : list α) (p : α → bool) : bool :=
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
| ((a, b) :: t) := match unzip t with | (al, bl) := (a::al, b::bl)

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

def repeat (a : α) (n : ℕ) : list α :=
n.repeat (λ _ xs, a :: xs) []

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

def last : Π l : list α, l ≠ [] → α
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

@[inline] protected def bind {α : Type u} {β : Type v} (a : list α) (b : α → list β) : list β :=
join (map b a)

@[inline] protected def ret {α : Type u} (a : α) : list α :=
[a]

protected def lt [has_lt α] : list α → list α → Prop
| []      []      := false
| []      (b::bs) := true
| (a::as) []      := false
| (a::as) (b::bs) := a < b ∨ (¬ b < a ∧ lt as bs)

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
    match h b a with
    | is_true h₂  := is_false (λ h, or.elim h (λ h, absurd h h₁) (λ ⟨h, _⟩, absurd h₂ h))
    | is_false h₂ :=
      match has_decidable_lt as bs with
      | is_true h₃  := is_true (or.inr ⟨h₂, h₃⟩)
      | is_false h₃ := is_false (λ h, or.elim h (λ h, absurd h h₁) (λ ⟨_, h⟩, absurd h h₃))

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

/--  `is_prefix_of l₁ l₂` returns `tt` iff `l₁` is a prefix of `l₂`. -/
def is_prefix_of [decidable_eq α] : list α → list α → bool
| []      _       := tt
| _       []      := ff
| (a::as) (b::bs) := to_bool (a = b) && is_prefix_of as bs

/--  `is_suffix_of l₁ l₂` returns `tt` iff `l₁` is a suffix of `l₂`. -/
def is_suffix_of [decidable_eq α] (l₁ l₂ : list α) : bool :=
is_prefix_of l₁.reverse l₂.reverse

end list

namespace bin_tree
private def to_list_aux : bin_tree α → list α → list α
| empty      as := as
| (leaf a)   as := a::as
| (node l r) as := to_list_aux l (to_list_aux r as)

def to_list (t : bin_tree α) : list α :=
to_list_aux t []
end bin_tree
