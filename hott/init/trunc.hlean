/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Floris van Doorn

Definition of is_trunc (n-truncatedness)

Ported from Coq HoTT.
-/

prelude
import .nat .logic .equiv .pathover
open eq nat sigma unit sigma.ops
--set_option class.force_new true

/- Truncation levels -/

inductive trunc_index : Type₀ :=
| minus_two : trunc_index
| succ : trunc_index → trunc_index

open trunc_index

/-
   notation for trunc_index is -2, -1, 0, 1, ...
   from 0 and up this comes from a coercion from num to trunc_index (via ℕ)
-/

notation `ℕ₋₂` := trunc_index -- input using \N-2

definition has_zero_trunc_index [instance] [priority 2000] : has_zero ℕ₋₂ :=
has_zero.mk (succ (succ minus_two))

definition has_one_trunc_index [instance] [priority 2000] : has_one ℕ₋₂ :=
has_one.mk (succ (succ (succ minus_two)))

namespace trunc_index

  notation `-1` := trunc_index.succ trunc_index.minus_two -- ISSUE: -1 gets printed as -2.+1?
  notation `-2` := trunc_index.minus_two
  postfix `.+1`:(max+1) := trunc_index.succ
  postfix `.+2`:(max+1) := λn, (n .+1 .+1)

  --addition, where we add two to the result
  definition add_plus_two [reducible] (n m : ℕ₋₂) : ℕ₋₂ :=
  trunc_index.rec_on m n (λ k l, l .+1)

  infix ` +2+ `:65 := trunc_index.add_plus_two

  -- addition of trunc_indices, where results smaller than -2 are changed to -2
  protected definition add (n m : ℕ₋₂) : ℕ₋₂ :=
  trunc_index.cases_on m
    (trunc_index.cases_on n -2 (λn', (trunc_index.cases_on n' -2 id)))
    (λm', trunc_index.cases_on m'
      (trunc_index.cases_on n -2 id)
      (add_plus_two n))

  /- we give a weird name to the reflexivity step to avoid overloading le.refl
     (which can be used if types.trunc is imported) -/
  inductive le (a : ℕ₋₂) : ℕ₋₂ → Type :=
  | tr_refl : le a a
  | step : Π {b}, le a b → le a (b.+1)

end trunc_index

definition has_le_trunc_index [instance] [priority 2000] : has_le ℕ₋₂ :=
has_le.mk trunc_index.le

attribute trunc_index.add [reducible]

definition has_add_trunc_index [instance] [priority 2000] : has_add ℕ₋₂ :=
has_add.mk trunc_index.add

namespace trunc_index

  definition sub_two [reducible] (n : ℕ) : ℕ₋₂ :=
  nat.rec_on n -2 (λ n k, k.+1)

  definition add_two [reducible] (n : ℕ₋₂) : ℕ :=
  trunc_index.rec_on n nat.zero (λ n k, nat.succ k)

  postfix `.-2`:(max+1) := sub_two
  postfix `.-1`:(max+1) := λn, (n .-2 .+1)

  definition of_nat [coercion] [reducible] (n : ℕ) : ℕ₋₂ :=
  n.-2.+2

  definition succ_le_succ {n m : ℕ₋₂} (H : n ≤ m) : n.+1 ≤ m.+1 :=
  by induction H with m H IH; apply le.tr_refl; exact le.step IH

  definition minus_two_le (n : ℕ₋₂) : -2 ≤ n :=
  by induction n with n IH; apply le.tr_refl; exact le.step IH
  protected definition le_refl (n : ℕ₋₂) : n ≤ n :=
  le.tr_refl n

end trunc_index open trunc_index

namespace is_trunc

  export [notation] [coercion] trunc_index

  /- truncated types -/

  /-
    Just as in Coq HoTT we define an internal version of contractibility and is_trunc, but we only
    use `is_trunc` and `is_contr`
  -/

  structure contr_internal (A : Type) :=
    (center : A)
    (center_eq : Π(a : A), center = a)

  definition is_trunc_internal (n : ℕ₋₂) : Type → Type :=
    trunc_index.rec_on n
      (λA, contr_internal A)
      (λn trunc_n A, (Π(x y : A), trunc_n (x = y)))

end is_trunc open is_trunc

structure is_trunc [class] (n : ℕ₋₂) (A : Type) :=
  (to_internal : is_trunc_internal n A)

open nat num trunc_index

namespace is_trunc

  abbreviation is_contr := is_trunc -2
  abbreviation is_prop := is_trunc -1
  abbreviation is_set  := is_trunc 0

  variables {A B : Type}

  definition is_trunc_succ_intro (A : Type) (n : ℕ₋₂) [H : ∀x y : A, is_trunc n (x = y)]
    : is_trunc n.+1 A :=
  is_trunc.mk (λ x y, !is_trunc.to_internal)

  definition is_trunc_eq [instance] [priority 1200]
    (n : ℕ₋₂) [H : is_trunc (n.+1) A] (x y : A) : is_trunc n (x = y) :=
  is_trunc.mk (is_trunc.to_internal (n.+1) A x y)

  /- contractibility -/

  definition is_contr.mk (center : A) (center_eq : Π(a : A), center = a) : is_contr A :=
  is_trunc.mk (contr_internal.mk center center_eq)

  definition center (A : Type) [H : is_contr A] : A :=
  contr_internal.center (is_trunc.to_internal -2 A)

  definition center_eq [H : is_contr A] (a : A) : !center = a :=
  contr_internal.center_eq (is_trunc.to_internal -2 A) a

  definition eq_of_is_contr [H : is_contr A] (x y : A) : x = y :=
  (center_eq x)⁻¹ ⬝ (center_eq y)

  definition prop_eq_of_is_contr {A : Type} [H : is_contr A] {x y : A} (p q : x = y) : p = q :=
  have K : ∀ (r : x = y), eq_of_is_contr x y = r, from (λ r, eq.rec_on r !con.left_inv),
  (K p)⁻¹ ⬝ K q

  theorem is_contr_eq {A : Type} [H : is_contr A] (x y : A) : is_contr (x = y) :=
  is_contr.mk !eq_of_is_contr (λ p, !prop_eq_of_is_contr)
  local attribute is_contr_eq [instance]

  /- truncation is upward close -/

  -- n-types are also (n+1)-types
  theorem is_trunc_succ [instance] [priority 900] (A : Type) (n : ℕ₋₂)
    [H : is_trunc n A] : is_trunc (n.+1) A :=
  trunc_index.rec_on n
    (λ A (H : is_contr A), !is_trunc_succ_intro)
    (λ n IH A (H : is_trunc (n.+1) A), @is_trunc_succ_intro _ _ (λ x y, IH _ _))
    A H
  --in the proof the type of H is given explicitly to make it available for class inference

  theorem is_trunc_of_le.{l} (A : Type.{l}) {n m : ℕ₋₂} (Hnm : n ≤ m)
    [Hn : is_trunc n A] : is_trunc m A :=
  begin
    induction Hnm with m Hnm IH,
    { exact Hn},
    { exact _}
  end

  definition is_trunc_of_imp_is_trunc {n : ℕ₋₂} (H : A → is_trunc (n.+1) A)
    : is_trunc (n.+1) A :=
  @is_trunc_succ_intro _ _ (λx y, @is_trunc_eq _ _ (H x) x y)

  definition is_trunc_of_imp_is_trunc_of_le {n : ℕ₋₂} (Hn : -1 ≤ n) (H : A → is_trunc n A)
    : is_trunc n A :=
  begin
    cases Hn with n' Hn': apply is_trunc_of_imp_is_trunc H
  end

  -- these must be definitions, because we need them to compute sometimes
  definition is_trunc_of_is_contr (A : Type) (n : ℕ₋₂) [H : is_contr A] : is_trunc n A :=
  trunc_index.rec_on n H (λn H, _)

  definition is_trunc_succ_of_is_prop (A : Type) (n : ℕ₋₂) [H : is_prop A]
      : is_trunc (n.+1) A :=
  is_trunc_of_le A (show -1 ≤ n.+1, from succ_le_succ (minus_two_le n))

  definition is_trunc_succ_succ_of_is_set (A : Type) (n : ℕ₋₂) [H : is_set A]
      : is_trunc (n.+2) A :=
  is_trunc_of_le A (show 0 ≤ n.+2, from succ_le_succ (succ_le_succ (minus_two_le n)))

  /- props -/

  definition is_prop.elim [H : is_prop A] (x y : A) : x = y :=
  !center

  definition is_contr_of_inhabited_prop {A : Type} [H : is_prop A] (x : A) : is_contr A :=
  is_contr.mk x (λy, !is_prop.elim)

  theorem is_prop_of_imp_is_contr {A : Type} (H : A → is_contr A) : is_prop A :=
  @is_trunc_succ_intro A -2
    (λx y,
      have H2 : is_contr A, from H x,
      !is_contr_eq)

  theorem is_prop.mk {A : Type} (H : ∀x y : A, x = y) : is_prop A :=
  is_prop_of_imp_is_contr (λ x, is_contr.mk x (H x))

  theorem is_prop_elim_self {A : Type} {H : is_prop A} (x : A) : is_prop.elim x x = idp :=
  !is_prop.elim

  /- sets -/

  theorem is_set.mk (A : Type) (H : ∀(x y : A) (p q : x = y), p = q) : is_set A :=
  @is_trunc_succ_intro _ _ (λ x y, is_prop.mk (H x y))

  definition is_set.elim [H : is_set A] ⦃x y : A⦄ (p q : x = y) : p = q :=
  !is_prop.elim

  /- instances -/

  definition is_contr_sigma_eq [instance] [priority 800] {A : Type} (a : A)
    : is_contr (Σ(x : A), a = x) :=
  is_contr.mk (sigma.mk a idp) (λp, sigma.rec_on p (λ b q, eq.rec_on q idp))

  definition is_contr_sigma_eq' [instance] [priority 800] {A : Type} (a : A)
    : is_contr (Σ(x : A), x = a) :=
  is_contr.mk (sigma.mk a idp) (λp, sigma.rec_on p (λ b q, eq.rec_on q idp))

  definition ap_pr1_center_eq_sigma_eq {A : Type} {a x : A} (p : a = x)
    : ap pr₁ (center_eq ⟨x, p⟩) = p :=
  by induction p; reflexivity

  definition ap_pr1_center_eq_sigma_eq' {A : Type} {a x : A} (p : x = a)
    : ap pr₁ (center_eq ⟨x, p⟩) = p⁻¹ :=
  by induction p; reflexivity

  definition is_contr_unit : is_contr unit :=
  is_contr.mk star (λp, unit.rec_on p idp)

  definition is_prop_empty : is_prop empty :=
  is_prop.mk (λx, !empty.elim x)

  local attribute is_contr_unit is_prop_empty [instance]

  definition is_trunc_unit [instance] (n : ℕ₋₂) : is_trunc n unit :=
  !is_trunc_of_is_contr

  definition is_trunc_empty [instance] (n : ℕ₋₂) : is_trunc (n.+1) empty :=
  !is_trunc_succ_of_is_prop

  /- interaction with equivalences -/

  section
  open is_equiv equiv

  definition is_contr_is_equiv_closed (f : A → B) [Hf : is_equiv f] [HA: is_contr A]
    : (is_contr B) :=
  is_contr.mk (f (center A)) (λp, eq_of_eq_inv !center_eq)

  definition is_contr_equiv_closed (H : A ≃ B) [HA: is_contr A] : is_contr B :=
  is_contr_is_equiv_closed (to_fun H)

  definition equiv_of_is_contr_of_is_contr [HA : is_contr A] [HB : is_contr B] : A ≃ B :=
  equiv.mk
    (λa, center B)
    (is_equiv.adjointify (λa, center B) (λb, center A) center_eq center_eq)

  theorem is_trunc_is_equiv_closed (n : ℕ₋₂) (f : A → B) [H : is_equiv f]
    [HA : is_trunc n A] : is_trunc n B :=
  trunc_index.rec_on n
    (λA (HA : is_contr A) B f (H : is_equiv f), is_contr_is_equiv_closed f)
    (λn IH A (HA : is_trunc n.+1 A) B f (H : is_equiv f), @is_trunc_succ_intro _ _ (λ x y : B,
      IH (f⁻¹ x = f⁻¹ y) _ (x = y) (ap f⁻¹)⁻¹ !is_equiv_inv))
    A HA B f H

  definition is_trunc_is_equiv_closed_rev (n : ℕ₋₂) (f : A → B) [H : is_equiv f]
    [HA : is_trunc n B] : is_trunc n A :=
  is_trunc_is_equiv_closed n f⁻¹

  definition is_trunc_equiv_closed (n : ℕ₋₂) (f : A ≃ B) [HA : is_trunc n A]
    : is_trunc n B :=
  is_trunc_is_equiv_closed n (to_fun f)

  definition is_trunc_equiv_closed_rev (n : ℕ₋₂) (f : A ≃ B) [HA : is_trunc n B]
    : is_trunc n A :=
  is_trunc_is_equiv_closed n (to_inv f)

  definition is_equiv_of_is_prop [constructor] [HA : is_prop A] [HB : is_prop B]
    (f : A → B) (g : B → A) : is_equiv f :=
  is_equiv.mk f g (λb, !is_prop.elim) (λa, !is_prop.elim) (λa, !is_set.elim)

  definition equiv_of_is_prop [constructor] [HA : is_prop A] [HB : is_prop B]
    (f : A → B) (g : B → A) : A ≃ B :=
  equiv.mk f (is_equiv_of_is_prop f g)

  definition equiv_of_iff_of_is_prop [unfold 5] [HA : is_prop A] [HB : is_prop B] (H : A ↔ B) : A ≃ B :=
  equiv_of_is_prop (iff.elim_left H) (iff.elim_right H)

  /- truncatedness of lift -/
  definition is_trunc_lift [instance] [priority 1450] (A : Type) (n : ℕ₋₂)
    [H : is_trunc n A] : is_trunc n (lift A) :=
  is_trunc_equiv_closed _ !equiv_lift

  end

  /- interaction with the Unit type -/

  open equiv
  /- A contractible type is equivalent to unit. -/
  variable (A)
  definition equiv_unit_of_is_contr [H : is_contr A] : A ≃ unit :=
  equiv.MK (λ (x : A), ⋆)
           (λ (u : unit), center A)
           (λ (u : unit), unit.rec_on u idp)
           (λ (x : A), center_eq x)

  /- interaction with pathovers -/
  variable {A}
  variables {C : A → Type}
            {a a₂ : A} (p : a = a₂)
            (c : C a) (c₂ : C a₂)

  definition is_prop.elimo [H : is_prop (C a)] : c =[p] c₂ :=
  pathover_of_eq_tr !is_prop.elim

  definition is_trunc_pathover [instance]
    (n : ℕ₋₂) [H : is_trunc (n.+1) (C a)] : is_trunc n (c =[p] c₂) :=
  is_trunc_equiv_closed_rev n !pathover_equiv_eq_tr

  variables {p c c₂}
  theorem is_set.elimo (q q' : c =[p] c₂) [H : is_set (C a)] : q = q' :=
  !is_prop.elim

  -- TODO: port "Truncated morphisms"

  /- truncated universe -/

end is_trunc

structure trunctype (n : ℕ₋₂) :=
  (carrier : Type)
  (struct : is_trunc n carrier)

notation n `-Type` := trunctype n
abbreviation Prop := -1-Type
abbreviation Set  := 0-Type

attribute trunctype.carrier [coercion]
attribute trunctype.struct [instance] [priority 1400]

protected abbreviation Prop.mk := @trunctype.mk -1
protected abbreviation Set.mk := @trunctype.mk (-1.+1)

protected definition trunctype.mk' [constructor] (n : ℕ₋₂) (A : Type) [H : is_trunc n A]
  : n-Type :=
trunctype.mk A H

namespace is_trunc

  definition tlift.{u v} [constructor] {n : ℕ₋₂} (A : trunctype.{u} n)
    : trunctype.{max u v} n :=
  trunctype.mk (lift A) !is_trunc_lift

end is_trunc
