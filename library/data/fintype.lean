/-
Copyright (c) 2015 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura

Finite type (type class)
-/
import data.list data.bool
open list bool unit decidable option function

structure fintype [class] (A : Type) : Type :=
(elems : list A) (unique : nodup elems) (complete : ∀ a, a ∈ elems)

definition fintype_unit [instance] : fintype unit :=
fintype.mk [star] dec_trivial (λ u, match u with star := dec_trivial end)

definition fintype_bool [instance] : fintype bool :=
fintype.mk [ff, tt]
  dec_trivial
  (λ b, match b with | tt := dec_trivial | ff := dec_trivial end)

definition fintype_product [instance] {A B : Type} : Π [h₁ : fintype A] [h₂ : fintype B], fintype (A × B)
| (fintype.mk e₁ u₁ c₁) (fintype.mk e₂ u₂ c₂) :=
  fintype.mk
    (cross_product e₁ e₂)
    (nodup_cross_product u₁ u₂)
    (λ p,
      match p with
      (a, b) := mem_cross_product (c₁ a) (c₂ b)
      end)

/- auxiliary function for finding 'a' s.t. f a ≠ g a -/
section find_discr
variables {A B : Type}
variable  [h : decidable_eq B]
include h
definition find_discr (f g : A → B) : list A → option A
| []     := none
| (a::l) := if f a = g a then find_discr l else some a

theorem find_discr_nil (f g : A → B) : find_discr f g [] = none :=
rfl

theorem find_discr_cons_of_ne {f g : A → B} {a : A} (l : list A) : f a ≠ g a → find_discr f g (a::l) = some a :=
assume ne, if_neg ne

theorem find_discr_cons_of_eq {f g : A → B} {a : A} (l : list A) : f a = g a → find_discr f g (a::l) = find_discr f g l :=
assume eq, if_pos eq

theorem ne_of_find_discr_eq_some {f g : A → B} {a : A} : ∀ {l}, find_discr f g l = some a → f a ≠ g a
| []     e := option.no_confusion e
| (x::l) e := by_cases
  (λ h : f x = g x,
     have aux : find_discr f g l = some a, by rewrite [find_discr_cons_of_eq l h at e]; exact e,
     ne_of_find_discr_eq_some aux)
  (λ h : f x ≠ g x,
     have aux : some x = some a, by rewrite [find_discr_cons_of_ne l h at e]; exact e,
     option.no_confusion aux (λ xeqa : x = a, eq.rec_on xeqa h))

theorem all_eq_of_find_discr_eq_none {f g : A → B} : ∀ {l}, find_discr f g l = none → ∀ a, a ∈ l → f a = g a
| []     e a i := absurd i !not_mem_nil
| (x::l) e a i := by_cases
  (λ fx_eq_gx : f x = g x,
    have aux : find_discr f g l = none, by rewrite [find_discr_cons_of_eq l fx_eq_gx at e]; exact e,
    or.elim (eq_or_mem_of_mem_cons i)
      (λ aeqx : a = x, by rewrite [-aeqx at fx_eq_gx]; exact fx_eq_gx)
      (λ ainl : a ∈ l, all_eq_of_find_discr_eq_none aux a ainl))
  (λ fx_ne_gx : f x ≠ g x,
    have aux : some x = none, by rewrite [find_discr_cons_of_ne l fx_ne_gx at e]; exact e,
    option.no_confusion aux)
end find_discr

definition decidable_eq_fun [instance] {A B : Type} [h₁ : fintype A] [h₂ : decidable_eq B] : decidable_eq (A → B) :=
λ f g,
  match h₁ with
  | fintype.mk e u c :=
    match find_discr f g e with
    | some a := λ h : find_discr f g e = some a, inr (λ f_eq_g : f = g, absurd (by rewrite f_eq_g) (ne_of_find_discr_eq_some h))
    | none   := λ h : find_discr f g e = none, inl (show f = g, from funext (λ a : A, all_eq_of_find_discr_eq_none h a (c a)))
    end rfl
  end
