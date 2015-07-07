/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Floris van Doorn

Definition of is_trunc (n-truncatedness)

Ported from Coq HoTT.
-/

--TODO: can we replace some definitions with a hprop as codomain by theorems?

prelude
import .logic .equiv .types .pathover
open eq nat sigma unit

namespace is_trunc

 /- Truncation levels -/

  inductive trunc_index : Type₀ :=
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

  definition leq (n m : trunc_index) : Type₀ :=
  trunc_index.rec_on n (λm, unit) (λ n p m, trunc_index.rec_on m (λ p, empty) (λ m q p, p m) p) m
  infix <= := trunc_index.leq
  infix ≤  := trunc_index.leq
  end trunc_index

  infix `+2+`:65 := trunc_index.add

  namespace trunc_index
  definition succ_le_succ {n m : trunc_index} (H : n ≤ m) : n.+1 ≤ m.+1 := H
  definition le_of_succ_le_succ {n m : trunc_index} (H : n.+1 ≤ m.+1) : n ≤ m := H
  definition minus_two_le (n : trunc_index) : -2 ≤ n := star
  definition empty_of_succ_le_minus_two {n : trunc_index} (H : n .+1 ≤ -2) : empty := H
  end trunc_index
  definition trunc_index.of_nat [coercion] [reducible] (n : nat) : trunc_index :=
  (nat.rec_on n -2 (λ n k, k.+1)).+2

  definition sub_two [reducible] (n : nat) : trunc_index :=
  nat.rec_on n -2 (λ n k, k.+1)

  postfix `.-2`:(max+1) := sub_two

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

end is_trunc open is_trunc
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

  definition hprop_eq_of_is_contr {A : Type} [H : is_contr A] {x y : A} (p q : x = y) : p = q :=
  have K : ∀ (r : x = y), eq_of_is_contr x y = r, from (λ r, eq.rec_on r !con.left_inv),
  (K p)⁻¹ ⬝ K q

  theorem is_contr_eq {A : Type} [H : is_contr A] (x y : A) : is_contr (x = y) :=
  is_contr.mk !eq_of_is_contr (λ p, !hprop_eq_of_is_contr)
  local attribute is_contr_eq [instance]

  /- truncation is upward close -/

  -- n-types are also (n+1)-types
  theorem is_trunc_succ [instance] [priority 900] (A : Type) (n : trunc_index)
    [H : is_trunc n A] : is_trunc (n.+1) A :=
  trunc_index.rec_on n
    (λ A (H : is_contr A), !is_trunc_succ_intro)
    (λ n IH A (H : is_trunc (n.+1) A), @is_trunc_succ_intro _ _ (λ x y, IH _ _))
    A H
  --in the proof the type of H is given explicitly to make it available for class inference

  theorem is_trunc_of_leq.{l} (A : Type.{l}) {n m : trunc_index} (Hnm : n ≤ m)
    [Hn : is_trunc n A] : is_trunc m A :=
  have base : ∀k A, k ≤ -2 → is_trunc k A → (is_trunc -2 A), from
    λ k A, trunc_index.cases_on k
           (λh1 h2, h2)
           (λk h1 h2, empty.elim (trunc_index.empty_of_succ_le_minus_two h1)),
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
  theorem is_trunc_of_is_contr (A : Type) (n : trunc_index) [H : is_contr A] : is_trunc n A :=
  trunc_index.rec_on n H _

  theorem is_trunc_succ_of_is_hprop (A : Type) (n : trunc_index) [H : is_hprop A]
      : is_trunc (n.+1) A :=
  is_trunc_of_leq A (show -1 ≤ n.+1, from star)

  theorem is_trunc_succ_succ_of_is_hset (A : Type) (n : trunc_index) [H : is_hset A]
      : is_trunc (n.+2) A :=
  is_trunc_of_leq A (show 0 ≤ n.+2, from star)

  /- hprops -/

  definition is_hprop.elim [H : is_hprop A] (x y : A) : x = y :=
  !center

  definition is_contr_of_inhabited_hprop {A : Type} [H : is_hprop A] (x : A) : is_contr A :=
  is_contr.mk x (λy, !is_hprop.elim)

  theorem is_hprop_of_imp_is_contr {A : Type} (H : A → is_contr A) : is_hprop A :=
  @is_trunc_succ_intro A -2
    (λx y,
      have H2 [visible] : is_contr A, from H x,
      !is_contr_eq)

  theorem is_hprop.mk {A : Type} (H : ∀x y : A, x = y) : is_hprop A :=
  is_hprop_of_imp_is_contr (λ x, is_contr.mk x (H x))

  theorem is_hprop_elim_self {A : Type} {H : is_hprop A} (x : A) : is_hprop.elim x x = idp :=
  !is_hprop.elim

  /- hsets -/

  theorem is_hset.mk (A : Type) (H : ∀(x y : A) (p q : x = y), p = q) : is_hset A :=
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

  -- TODO: move to root namespace?
  structure trunctype (n : trunc_index) :=
  (carrier : Type) (struct : is_trunc n carrier)
  attribute trunctype.carrier [coercion]
  attribute trunctype.struct [instance]

  notation n `-Type` := trunctype n
  abbreviation hprop := -1-Type
  abbreviation hset := 0-Type

  protected abbreviation hprop.mk := @trunctype.mk -1
  protected abbreviation hset.mk := @trunctype.mk (-1.+1)

  protected abbreviation trunctype.mk' [parsing-only] (n : trunc_index) (A : Type)
    [H : is_trunc n A] : n-Type :=
  trunctype.mk A H

  /- interaction with equivalences -/

  section
  open is_equiv equiv

  --should we remove the following two theorems as they are special cases of
  --"is_trunc_is_equiv_closed"
  definition is_contr_is_equiv_closed (f : A → B) [Hf : is_equiv f] [HA: is_contr A]
    : (is_contr B) :=
  is_contr.mk (f (center A)) (λp, eq_of_eq_inv !center_eq)

  definition is_contr_equiv_closed (H : A ≃ B) [HA: is_contr A] : is_contr B :=
  is_contr_is_equiv_closed (to_fun H)

  definition equiv_of_is_contr_of_is_contr [HA : is_contr A] [HB : is_contr B] : A ≃ B :=
  equiv.mk
    (λa, center B)
    (is_equiv.adjointify (λa, center B) (λb, center A) center_eq center_eq)

  theorem is_trunc_is_equiv_closed (n : trunc_index) (f : A → B) [H : is_equiv f]
    [HA : is_trunc n A] : is_trunc n B :=
  trunc_index.rec_on n
    (λA (HA : is_contr A) B f (H : is_equiv f), is_contr_is_equiv_closed f)
    (λn IH A (HA : is_trunc n.+1 A) B f (H : is_equiv f), @is_trunc_succ_intro _ _ (λ x y : B,
      IH (f⁻¹ x = f⁻¹ y) _ (x = y) (ap f⁻¹)⁻¹ !is_equiv_inv))
    A HA B f H

  definition is_trunc_is_equiv_closed_rev (n : trunc_index) (f : A → B) [H : is_equiv f]
    [HA : is_trunc n B] : is_trunc n A :=
  is_trunc_is_equiv_closed n f⁻¹

  definition is_trunc_equiv_closed (n : trunc_index) (f : A ≃ B) [HA : is_trunc n A]
    : is_trunc n B :=
  is_trunc_is_equiv_closed n (to_fun f)

  definition is_trunc_equiv_closed_rev (n : trunc_index) (f : A ≃ B) [HA : is_trunc n B]
    : is_trunc n A :=
  is_trunc_is_equiv_closed n (to_inv f)

  definition is_equiv_of_is_hprop [constructor] [HA : is_hprop A] [HB : is_hprop B]
    (f : A → B) (g : B → A) : is_equiv f :=
  is_equiv.mk f g (λb, !is_hprop.elim) (λa, !is_hprop.elim) (λa, !is_hset.elim)

  definition equiv_of_is_hprop [constructor] [HA : is_hprop A] [HB : is_hprop B]
    (f : A → B) (g : B → A) : A ≃ B :=
  equiv.mk f (is_equiv_of_is_hprop f g)

  definition equiv_of_iff_of_is_hprop [unfold 5] [HA : is_hprop A] [HB : is_hprop B] (H : A ↔ B) : A ≃ B :=
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

  /- interaction with pathovers -/
  variables {C : A → Type}
            {a a₂ : A} (p : a = a₂)
            (c : C a) (c₂ : C a₂)

  definition is_hprop.elimo [H : is_hprop (C a)] : c =[p] c₂ :=
  pathover_of_eq_tr !is_hprop.elim

  definition is_trunc_pathover [instance]
    (n : trunc_index) [H : is_trunc (n.+1) (C a)] : is_trunc n (c =[p] c₂) :=
  is_trunc_equiv_closed_rev n !pathover_equiv_eq_tr

  variables {p c c₂}
  theorem is_hset.elimo (q q' : c =[p] c₂) [H : is_hset (C a)] : q = q' :=
  !is_hprop.elim

  -- TODO: port "Truncated morphisms"

end is_trunc
