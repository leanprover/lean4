/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: init.trunc
Authors: Jeremy Avigad, Floris van Doorn

Definition of is_trunc (n-truncatedness)

Ported from Coq HoTT.
-/

--TODO: can we replace some definitions with a hprop as codomain by theorems?

prelude
import .logic .equiv .types
open eq nat sigma unit

namespace is_trunc

 /- Truncation levels -/

  inductive trunc_index : Type₁ :=
  | minus_two : trunc_index
  | succ : trunc_index → trunc_index

  /-
     notation for trunc_index is -2, -1, 0, 1, ...
     from 0 and up this comes from a coercion from num to trunc_index (via nat)
  -/
  postfix `.+1`:(max+1) := trunc_index.succ
  postfix `.+2`:(max+1) := λn, (n .+1 .+1)
  notation `-2` := trunc_index.minus_two
  notation `-1` := -2.+1 -- ISSUE: -1 gets printed as -2.+1
  export [coercions] nat

  namespace trunc_index
  definition add (n m : trunc_index) : trunc_index :=
  trunc_index.rec_on m n (λ k l, l .+1)

  definition leq (n m : trunc_index) : Type₁ :=
  trunc_index.rec_on n (λm, unit) (λ n p m, trunc_index.rec_on m (λ p, empty) (λ m q p, p m) p) m
  end trunc_index

  infix `+2+`:65 := trunc_index.add

  notation x <= y := trunc_index.leq x y
  notation x ≤ y := trunc_index.leq x y

  namespace trunc_index
  definition succ_le_succ {n m : trunc_index} (H : n ≤ m) : n.+1 ≤ m.+1 := H
  definition le_of_succ_le_succ {n m : trunc_index} (H : n.+1 ≤ m.+1) : n ≤ m := H
  definition minus_two_le (n : trunc_index) : -2 ≤ n := star
  definition empty_of_succ_le_minus_two {n : trunc_index} (H : n .+1 ≤ -2) : empty := H
  end trunc_index
  definition trunc_index.of_nat [coercion] [reducible] (n : nat) : trunc_index :=
  nat.rec_on n (-1.+1) (λ n k, k.+1)

  /- truncated types -/

  /-
    Just as in Coq HoTT we define an internal version of contractibility and is_trunc, but we only
    use `is_trunc` and `is_contr`
  -/

  structure contr_internal (A : Type) :=
    (center : A)
    (center_eq : Π(a : A), center = a)

  definition is_trunc_internal (n : trunc_index) : Type → Type :=
    trunc_index.rec_on n
      (λA, contr_internal A)
      (λn trunc_n A, (Π(x y : A), trunc_n (x = y)))

end is_trunc

open is_trunc
structure is_trunc [class] (n : trunc_index) (A : Type) :=
  (to_internal : is_trunc_internal n A)
open nat num is_trunc.trunc_index
namespace is_trunc

  abbreviation is_contr := is_trunc -2
  abbreviation is_hprop := is_trunc -1
  abbreviation is_hset  := is_trunc 0

  variables {A B : Type}

  definition is_trunc_succ_intro (A : Type) (n : trunc_index) [H : ∀x y : A, is_trunc n (x = y)]
    : is_trunc n.+1 A :=
  is_trunc.mk (λ x y, !is_trunc.to_internal)

  definition is_trunc_eq [instance] [priority 1200]
    (n : trunc_index) [H : is_trunc (n.+1) A] (x y : A) : is_trunc n (x = y) :=
  is_trunc.mk (!is_trunc.to_internal x y)

  /- contractibility -/

  definition is_contr.mk (center : A) (center_eq : Π(a : A), center = a) : is_contr A :=
  is_trunc.mk (contr_internal.mk center center_eq)

  definition center (A : Type) [H : is_contr A] : A :=
  @contr_internal.center A !is_trunc.to_internal

  definition center_eq [H : is_contr A] (a : A) : !center = a :=
  @contr_internal.center_eq A !is_trunc.to_internal a

  definition eq_of_is_contr [H : is_contr A] (x y : A) : x = y :=
  (center_eq x)⁻¹ ⬝ (center_eq y)

  definition hprop_eq_of_is_contr {A : Type} [H : is_contr A] {x y : A} (p q : x = y) : p = q :=
  have K : ∀ (r : x = y), eq_of_is_contr x y = r, from (λ r, eq.rec_on r !con.left_inv),
  (K p)⁻¹ ⬝ K q

  definition is_contr_eq {A : Type} [H : is_contr A] (x y : A) : is_contr (x = y) :=
  is_contr.mk !eq_of_is_contr (λ p, !hprop_eq_of_is_contr)
  local attribute is_contr_eq [instance]

  /- truncation is upward close -/

  -- n-types are also (n+1)-types
  definition is_trunc_succ [instance] [priority 900] (A : Type) (n : trunc_index)
    [H : is_trunc n A] : is_trunc (n.+1) A :=
  trunc_index.rec_on n
    (λ A (H : is_contr A), !is_trunc_succ_intro)
    (λ n IH A (H : is_trunc (n.+1) A), @is_trunc_succ_intro _ _ (λ x y, IH _ _))
    A H
  --in the proof the type of H is given explicitly to make it available for class inference

  definition is_trunc_of_leq (A : Type) (n m : trunc_index) (Hnm : n ≤ m)
    [Hn : is_trunc n A] : is_trunc m A :=
  have base : ∀k A, k ≤ -2 → is_trunc k A → (is_trunc -2 A), from
    λ k A, trunc_index.cases_on k
           (λh1 h2, h2)
           (λk h1 h2, empty.elim (is_trunc -2 A) (trunc_index.empty_of_succ_le_minus_two h1)),
  have step : Π (m : trunc_index)
                (IHm : Π (n : trunc_index) (A : Type), n ≤ m → is_trunc n A → is_trunc m A)
                (n : trunc_index) (A : Type)
                (Hnm : n ≤ m .+1) (Hn : is_trunc n A), is_trunc m .+1 A, from
    λm IHm n, trunc_index.rec_on n
           (λA Hnm Hn, @is_trunc_succ A m (IHm -2 A star Hn))
           (λn IHn A Hnm (Hn : is_trunc n.+1 A),
           @is_trunc_succ_intro A m (λx y, IHm n (x = y) (trunc_index.le_of_succ_le_succ Hnm) _)),
  trunc_index.rec_on m base step n A Hnm Hn

  -- the following cannot be instances in their current form, because they are looping
  definition is_trunc_of_is_contr (A : Type) (n : trunc_index) [H : is_contr A] : is_trunc n A :=
  trunc_index.rec_on n H _

  definition is_trunc_succ_of_is_hprop (A : Type) (n : trunc_index) [H : is_hprop A]
      : is_trunc (n.+1) A :=
  is_trunc_of_leq A -1 (n.+1) star

  definition is_trunc_succ_succ_of_is_hset (A : Type) (n : trunc_index) [H : is_hset A]
      : is_trunc (n.+2) A :=
  is_trunc_of_leq A nat.zero (n.+2) star

  /- hprops -/

  definition is_hprop.elim [H : is_hprop A] (x y : A) : x = y :=
  !center

  definition is_contr_of_inhabited_hprop {A : Type} [H : is_hprop A] (x : A) : is_contr A :=
  is_contr.mk x (λy, !is_hprop.elim)

  --Coq has the following as instance, but doesn't look too useful
  definition is_hprop_of_imp_is_contr {A : Type} (H : A → is_contr A) : is_hprop A :=
  @is_trunc_succ_intro A -2
    (λx y,
      have H2 [visible] : is_contr A, from H x,
      !is_contr_eq)

  definition is_hprop.mk {A : Type} (H : ∀x y : A, x = y) : is_hprop A :=
  is_hprop_of_imp_is_contr (λ x, is_contr.mk x (H x))

  /- hsets -/

  definition is_hset.mk (A : Type) (H : ∀(x y : A) (p q : x = y), p = q) : is_hset A :=
  @is_trunc_succ_intro _ _ (λ x y, is_hprop.mk (H x y))

  definition is_hset.elim [H : is_hset A] ⦃x y : A⦄ (p q : x = y) : p = q :=
  !is_hprop.elim

  /- instances -/

  definition is_contr_sigma_eq [instance] [priority 800] {A : Type} (a : A)
    : is_contr (Σ(x : A), a = x) :=
  is_contr.mk (sigma.mk a idp) (λp, sigma.rec_on p (λ b q, eq.rec_on q idp))

  definition is_contr_unit [instance] : is_contr unit :=
  is_contr.mk star (λp, unit.rec_on p idp)

  definition is_hprop_empty [instance] : is_hprop empty :=
  is_hprop.mk (λx, !empty.elim x)

  /- truncated universe -/

  structure trunctype (n : trunc_index) :=
  (carrier : Type) (struct : is_trunc n carrier)
  attribute trunctype.carrier [coercion]
  attribute trunctype.struct [instance]

  notation n `-Type` := trunctype n
  abbreviation hprop := -1-Type
  abbreviation hset := 0-Type

  protected definition hprop.mk := @trunctype.mk -1
  protected definition hset.mk := @trunctype.mk (-1.+1)

  /- interaction with equivalences -/

  section
  open is_equiv equiv

  --should we remove the following two theorems as they are special cases of
  --"is_trunc_is_equiv_closed"
  definition is_contr_is_equiv_closed (f : A → B) [Hf : is_equiv f] [HA: is_contr A]
    : (is_contr B) :=
  is_contr.mk (f (center A)) (λp, eq_of_eq_inv !center_eq)

  theorem is_contr_equiv_closed (H : A ≃ B) [HA: is_contr A] : is_contr B :=
  @is_contr_is_equiv_closed _ _ (to_fun H) (to_is_equiv H) _

  definition equiv_of_is_contr_of_is_contr [HA : is_contr A] [HB : is_contr B] : A ≃ B :=
  equiv.mk
    (λa, center B)
    (is_equiv.adjointify (λa, center B) (λb, center A) center_eq center_eq)

  definition is_trunc_is_equiv_closed (n : trunc_index) (f : A → B) [H : is_equiv f]
    [HA : is_trunc n A] : is_trunc n B :=
  trunc_index.rec_on n
    (λA (HA : is_contr A) B f (H : is_equiv f), !is_contr_is_equiv_closed)
    (λn IH A (HA : is_trunc n.+1 A) B f (H : is_equiv f), @is_trunc_succ_intro _ _ (λ x y : B,
      IH (f⁻¹ x = f⁻¹ y) _ (x = y) (ap f⁻¹)⁻¹ !is_equiv_inv))
    A HA B f H

  definition is_trunc_equiv_closed (n : trunc_index) (f : A ≃ B) [HA : is_trunc n A]
    : is_trunc n B :=
  is_trunc_is_equiv_closed n (to_fun f)

  definition is_equiv_of_is_hprop [HA : is_hprop A] [HB : is_hprop B] (f : A → B) (g : B → A)
    : is_equiv f :=
  is_equiv.mk f g (λb, !is_hprop.elim) (λa, !is_hprop.elim) (λa, !is_hset.elim)

  definition equiv_of_is_hprop [HA : is_hprop A] [HB : is_hprop B] (f : A → B) (g : B → A)
    : A ≃ B :=
  equiv.mk f (is_equiv_of_is_hprop f g)

  definition equiv_of_iff_of_is_hprop [HA : is_hprop A] [HB : is_hprop B] (H : A ↔ B) : A ≃ B :=
  equiv_of_is_hprop (iff.elim_left H) (iff.elim_right H)

  end

  /- interaction with the Unit type -/

  open equiv
  -- A contractible type is equivalent to [Unit]. *)
  definition equiv_unit_of_is_contr [H : is_contr A] : A ≃ unit :=
  equiv.MK (λ (x : A), ⋆)
           (λ (u : unit), center A)
           (λ (u : unit), unit.rec_on u idp)
           (λ (x : A), center_eq x)

  -- TODO: port "Truncated morphisms"

end is_trunc
