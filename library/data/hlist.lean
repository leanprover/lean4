/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

Heterogeneous lists
-/
import data.list logic.cast
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

lemma append_nil_left : ∀ {l} (h : hlist B l), append nil h = h :=
by intros; reflexivity

open eq.ops
lemma eq_rec_on_cons : ∀ {a₁ a₂ l₁ l₂} (b : B a₁) (h : hlist B l₁) (e : a₁::l₁ = a₂::l₂),
                         e ▹ cons b h = cons (head_eq_of_cons_eq e ▹ b) (tail_eq_of_cons_eq e ▹ h) :=
begin
  intros, injection e with e₁ e₂, revert e, subst a₂, subst l₂, intro e, esimp
end

lemma append_nil_right : ∀ {l} (h : hlist B l), append h nil = (list.append_nil_right l)⁻¹ ▹ h
| []     nil        := by esimp
| (a::l) (cons b h) :=
  begin
    unfold append, rewrite [append_nil_right h], xrewrite eq_rec_on_cons
  end

lemma append_nil_right_heq {l} (h : hlist B l) : append h nil == h :=
by rewrite append_nil_right; apply eq_rec_heq

section get
variables [decA : decidable_eq A]
include decA

definition get {a : A} : ∀ {l : list A}, hlist B l → a ∈ l → B a
| []     nil        e := absurd e !not_mem_nil
| (t::l) (cons b h) e :=
  or.by_cases (eq_or_mem_of_mem_cons e)
    (suppose a = t, by subst t; exact b)
    (suppose a ∈ l, get h this)
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
