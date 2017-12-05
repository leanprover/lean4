/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
universes u v w

inductive lazy_list (α : Type u) : Type u
| nil {} : lazy_list
| cons (hd : α) (tl : thunk lazy_list) : lazy_list

namespace lazy_list
variables {α : Type u} {β : Type v} {δ : Type w}

def singleton : α → lazy_list α
| a := cons a nil

def of_list : list α → lazy_list α
| []     := nil
| (h::t) := cons h (of_list t)

def to_list : lazy_list α → list α
| nil        := []
| (cons h t) := h :: to_list (t ())

def head [inhabited α] : lazy_list α → α
| nil        := default α
| (cons h t) := h

def tail : lazy_list α → lazy_list α
| nil        := nil
| (cons h t) := t ()

def append : lazy_list α → thunk (lazy_list α) → lazy_list α
| nil        l  := l ()
| (cons h t) l  := cons h (@append (t ()) l)

def map (f : α → β) : lazy_list α → lazy_list β
| nil        := nil
| (cons h t) := cons (f h) (map (t ()))

def map₂ (f : α → β → δ) : lazy_list α → lazy_list β → lazy_list δ
| nil          _            := nil
| _            nil          := nil
| (cons h₁ t₁) (cons h₂ t₂) := cons (f h₁ h₂) (map₂ (t₁ ()) (t₂ ()))

def zip : lazy_list α → lazy_list β → lazy_list (α × β) :=
map₂ prod.mk

def join : lazy_list (lazy_list α) → lazy_list α
| nil        := nil
| (cons h t) := append h (join (t ()))

def for (l : lazy_list α) (f : α → β) : lazy_list β :=
map f l

def approx : nat → lazy_list α → list α
| 0     l          := []
| _     nil        := []
| (a+1) (cons h t) := h :: approx a (t ())

def filter (p : α → Prop) [decidable_pred p] : lazy_list α → lazy_list α
| nil        := nil
| (cons h t) := if p h then cons h (filter (t ())) else filter (t ())

def nth : lazy_list α → nat → option α
| nil        n     := none
| (cons a l) 0     := some a
| (cons a l) (n+1) := nth (l ()) n

/- This definition must be meta because it uses unbounded recursion -/
meta def iterates (f : α → α) : α → lazy_list α
| x := cons x (iterates (f x))

meta def iota (i : nat) : lazy_list nat :=
iterates nat.succ i

end lazy_list
