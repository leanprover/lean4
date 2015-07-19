/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

Heterogeneous lists
-/
import data.list
open list

inductive hlist {A : Type} (B : A → Type) : list A → Type :=
| nil {} : hlist B []
| cons   : ∀ {a : A}, B a → ∀ {l : list A}, hlist B l → hlist B (a::l)

namespace hlist
variables {A : Type} {B : A → Type}

definition head : Π {a l}, hlist B (a :: l) → B a
| a l (cons b h) := b

lemma head_cons : ∀ {a l} (b : B a) (h : hlist B l), head (cons b h) = b :=
by intros; reflexivity

definition tail : Π {a l}, hlist B (a :: l) → hlist B l
| a l (cons b h) := h

lemma tail_cons : ∀ {a l} (b : B a) (h : hlist B l), tail (cons b h) = h :=
by intros; reflexivity

lemma eta_cons : ∀ {a l} (h : hlist B (a::l)), h = cons (head h) (tail h) :=
begin intros, cases h, esimp end

lemma eta_nil : ∀ (h : hlist B []), h = nil :=
begin intros, cases h, esimp end

definition append : Π {l₁ l₂}, hlist B l₁ → hlist B l₂ → hlist B (l₁++l₂)
| ⌞[]⌟    l₂ nil         h₂ := h₂
| ⌞a::l₁⌟ l₂ (cons b h₁) h₂ := cons b (append h₁ h₂)

lemma append_left_nil : ∀ {l} (h : hlist B l), append nil h = h :=
by intros; reflexivity

lemma append_right_nil : ∀ {l} (h : hlist B l), append h nil == h
| []     nil        := !heq.refl
| (a::l) (cons b h) :=
  begin
    unfold append,
    have ih  : append h nil == h, from append_right_nil h,
    have aux : l ++ [] = l,       from list.append_nil_right l,
    revert ih, generalize append h nil,
    esimp [list.append], rewrite aux,
    intro x ih,
    rewrite [heq.to_eq ih]
  end

section get
variables [decA : decidable_eq A]
include decA

definition get {a : A} : ∀ {l : list A}, hlist B l → a ∈ l → B a
| []     nil        e := absurd e !not_mem_nil
| (t::l) (cons b h) e :=
  or.by_cases (eq_or_mem_of_mem_cons e)
    (λ aeqt, by subst t; exact b)
    (λ ainl, get h ainl)
end get

section map
variable {C : A → Type}
variable (f : Π ⦃a⦄, B a → C a)

definition map : ∀ {l}, hlist B l → hlist C l
| ⌞[]⌟   nil        := nil
| ⌞a::l⌟ (cons b h) := cons (f b) (map h)

lemma map_nil : map f nil = nil :=
rfl

lemma map_cons : ∀ {a l} (b : B a) (h : hlist B l), map f (cons b h) = cons (f b) (map f h) :=
by intros; reflexivity
end map
end hlist
