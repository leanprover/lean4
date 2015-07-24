/-
Copyright (c) 2015 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Finite type (type class).
-/
import data.list.perm data.list.as_type data.bool data.equiv
open list bool unit decidable option function

structure fintype [class] (A : Type) : Type :=
(elems : list A) (unique : nodup elems) (complete : ∀ a, a ∈ elems)

definition elements_of (A : Type) [h : fintype A] : list A :=
@fintype.elems A h

section
open equiv
definition fintype_of_equiv {A B : Type} [h : fintype A] : A ≃ B → fintype B
| (mk f g l r) :=
  fintype.mk
    (map f (elements_of A))
    (nodup_map (injective_of_left_inverse l) !fintype.unique)
    (λ b,
      have g b ∈ elements_of A, from fintype.complete (g b),
      assert f (g b) ∈ map f (elements_of A), from mem_map f this,
      by rewrite r at this; exact this)
end

definition fintype_unit [instance] : fintype unit :=
fintype.mk [star] dec_trivial (λ u, match u with star := dec_trivial end)

definition fintype_bool [instance] : fintype bool :=
fintype.mk [ff, tt]
  dec_trivial
  (λ b, match b with | tt := dec_trivial | ff := dec_trivial end)

definition fintype_product [instance] {A B : Type} : Π [h₁ : fintype A] [h₂ : fintype B], fintype (A × B)
| (fintype.mk e₁ u₁ c₁) (fintype.mk e₂ u₂ c₂) :=
  fintype.mk
    (product e₁ e₂)
    (nodup_product u₁ u₂)
    (λ p,
      match p with
      (a, b) := mem_product (c₁ a) (c₂ b)
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
| []     e := by contradiction
| (x::l) e := by_cases
  (suppose f x = g x,
     have find_discr f g l = some a, by rewrite [find_discr_cons_of_eq l this at e]; exact e,
     ne_of_find_discr_eq_some this)
  (assume h : f x ≠ g x,
     assert some x = some a, by rewrite [find_discr_cons_of_ne l h at e]; exact e,
     by clear ne_of_find_discr_eq_some; injection this; subst a; exact h)

theorem all_eq_of_find_discr_eq_none {f g : A → B} : ∀ {l}, find_discr f g l = none → ∀ a, a ∈ l → f a = g a
| []     e a i := absurd i !not_mem_nil
| (x::l) e a i := by_cases
  (assume fx_eq_gx : f x = g x,
    or.elim (eq_or_mem_of_mem_cons i)
      (suppose a = x, by rewrite [-this at fx_eq_gx]; exact fx_eq_gx)
      (suppose a ∈ l,
        have aux : find_discr f g l = none, by rewrite [find_discr_cons_of_eq l fx_eq_gx at e]; exact e,
        all_eq_of_find_discr_eq_none aux a this))
  (suppose f x ≠ g x,
    by rewrite [find_discr_cons_of_ne l this at e]; contradiction)
end find_discr

definition decidable_eq_fun [instance] {A B : Type} [h₁ : fintype A] [h₂ : decidable_eq B] : decidable_eq (A → B) :=
λ f g,
  match h₁ with
  | fintype.mk e u c :=
    match find_discr f g e with
    | some a := λ h : find_discr f g e = some a, inr (λ f_eq_g : f = g, absurd (by rewrite f_eq_g; reflexivity) (ne_of_find_discr_eq_some h))
    | none   := λ h : find_discr f g e = none, inl (show f = g, from funext (λ a : A, all_eq_of_find_discr_eq_none h a (c a)))
    end rfl
  end

section check_pred
variables {A : Type}

definition check_pred (p : A → Prop) [h : decidable_pred p] : list A → bool
| []     := tt
| (a::l) := if p a then check_pred l else ff

theorem check_pred_cons_of_pos {p : A → Prop} [h : decidable_pred p] {a : A} (l : list A) : p a → check_pred p (a::l) = check_pred p l :=
assume pa, if_pos pa

theorem check_pred_cons_of_neg {p : A → Prop} [h : decidable_pred p] {a : A} (l : list A) : ¬ p a → check_pred p (a::l) = ff :=
assume npa, if_neg npa

theorem all_of_check_pred_eq_tt {p : A → Prop} [h : decidable_pred p] : ∀ {l : list A}, check_pred p l = tt → ∀ {a}, a ∈ l → p a
| []     eqtt a ainl := absurd ainl !not_mem_nil
| (b::l) eqtt a ainbl := by_cases
  (suppose p b, or.elim (eq_or_mem_of_mem_cons ainbl)
    (suppose a = b, by rewrite [this]; exact `p b`)
    (suppose a ∈ l,
      have check_pred p l = tt, by rewrite [check_pred_cons_of_pos _ `p b` at eqtt]; exact eqtt,
      all_of_check_pred_eq_tt this `a ∈ l`))
  (suppose ¬ p b,
    by rewrite [check_pred_cons_of_neg _ this at eqtt]; exact (bool.no_confusion eqtt))

theorem ex_of_check_pred_eq_ff {p : A → Prop} [h : decidable_pred p] : ∀ {l : list A}, check_pred p l = ff → ∃ w, ¬ p w
| []     eqtt := bool.no_confusion eqtt
| (a::l) eqtt := by_cases
  (suppose p a,
    have check_pred p l = ff, by rewrite [check_pred_cons_of_pos _ this at eqtt]; exact eqtt,
    ex_of_check_pred_eq_ff this)
  (suppose ¬ p a, exists.intro a this)
end check_pred

definition decidable_forall_finite [instance] {A : Type} {p : A → Prop} [h₁ : fintype A] [h₂ : decidable_pred p]
           : decidable (∀ x : A, p x) :=
match h₁ with
| fintype.mk e u c :=
  match check_pred p e with
  | tt := suppose check_pred p e = tt, inl (take a : A, all_of_check_pred_eq_tt this (c a))
  | ff := suppose check_pred p e = ff,
    inr (suppose ∀ x, p x,
         obtain (a : A) (w : ¬ p a), from ex_of_check_pred_eq_ff `check_pred p e = ff`,
         absurd (this a) w)
  end rfl
end

definition decidable_exists_finite [instance] {A : Type} {p : A → Prop} [h₁ : fintype A] [h₂ : decidable_pred p]
           : decidable (∃ x : A, p x) :=
match h₁ with
| fintype.mk e u c :=
  match check_pred (λ a, ¬ p a) e with
  | tt := λ h : check_pred (λ a, ¬ p a) e = tt, inr (λ ex : (∃ x, p x),
          obtain x px, from ex,
          absurd px (all_of_check_pred_eq_tt h (c x)))
  | ff := λ h : check_pred (λ a, ¬ p a) e = ff, inl (
          assert ∃ x, ¬¬p x, from ex_of_check_pred_eq_ff h,
          obtain x nnpx, from this, exists.intro x (not_not_elim nnpx))
  end rfl
end

open list.as_type
-- Auxiliary function for returning a list with all elements of the type: (list.as_type l)
-- Remark ⟪s⟫ is notation for (list.as_type l)
-- We use this function to define the instance for (fintype ⟪s⟫)
private definition ltype_elems {A : Type} {s : list A} : Π {l : list A}, l ⊆ s → list ⟪s⟫
| []     h := []
| (a::l) h := lval a (h a !mem_cons) :: ltype_elems (sub_of_cons_sub h)

private theorem mem_of_mem_ltype_elems {A : Type} {a : A} {s : list A}
                : Π {l : list A} {h : l ⊆ s} {m : a ∈ s}, mk a m ∈ ltype_elems h → a ∈ l
| []     h m lin := absurd lin !not_mem_nil
| (b::l) h m lin := or.elim (eq_or_mem_of_mem_cons lin)
  (suppose mk a m = mk b (h b (mem_cons b l)),
     as_type.no_confusion this (λ aeqb em, by rewrite [aeqb]; exact !mem_cons))
  (suppose mk a m ∈ ltype_elems (sub_of_cons_sub h),
     have a ∈ l, from mem_of_mem_ltype_elems this,
     mem_cons_of_mem _ this)

private theorem nodup_ltype_elems {A : Type} {s : list A} : Π {l : list A} (d : nodup l) (h : l ⊆ s), nodup (ltype_elems h)
| []     d h := nodup_nil
| (a::l) d h :=
  have d₁    : nodup l, from nodup_of_nodup_cons d,
  have nainl : a ∉ l, from not_mem_of_nodup_cons d,
  let  h₁    : l ⊆ s := sub_of_cons_sub h in
  have d₂    : nodup (ltype_elems h₁), from nodup_ltype_elems d₁ h₁,
  have nin   : mk a (h a (mem_cons a l)) ∉ ltype_elems h₁, from
    assume ab, absurd (mem_of_mem_ltype_elems ab) nainl,
  nodup_cons nin d₂

private theorem mem_ltype_elems {A : Type} {s : list A} {a : ⟪s⟫}
                : Π {l : list A} (h : l ⊆ s), value a ∈ l → a ∈ ltype_elems h
| []     h vainl  := absurd vainl !not_mem_nil
| (b::l) h vainbl := or.elim (eq_or_mem_of_mem_cons vainbl)
  (λ vaeqb : value a = b,
   begin
      revert vaeqb h,
      -- TODO(Leo): check why 'cases a with va, ma' produces an incorrect proof
      eapply as_type.cases_on a,
      intro va ma vaeqb,
      rewrite -vaeqb, intro h,
      apply mem_cons
   end)
  (λ vainl : value a ∈ l,
     have aux : a ∈ ltype_elems (sub_of_cons_sub h), from mem_ltype_elems (sub_of_cons_sub h) vainl,
     mem_cons_of_mem _ aux)

definition fintype_list_as_type [instance] {A : Type} [h : decidable_eq A] {s : list A} : fintype ⟪s⟫ :=
let  nds   : list A := erase_dup s in
have sub₁  : nds ⊆ s,   from erase_dup_sub s,
have sub₂  : s ⊆ nds,   from sub_erase_dup s,
have dnds  : nodup nds, from nodup_erase_dup s,
let  e     : list ⟪s⟫ := ltype_elems sub₁ in
fintype.mk
  e
  (nodup_ltype_elems dnds sub₁)
  (take a : ⟪s⟫,
   show a ∈ e, from
     have value a ∈ s,   from is_member a,
     have value a ∈ nds, from sub₂ this,
     mem_ltype_elems sub₁ this)
