-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Jeremy Avigad, Floris van Doorn
-- Ported from Coq HoTT
prelude
import .path .logic .datatypes .equiv .types.empty .types.sigma
open eq nat sigma unit
set_option pp.universes true

-- Truncation levels
-- -----------------

-- TODO: make everything universe polymorphic

-- TODO: everything definition with a hprop as codomain can be a theorem?

/- truncation indices -/

namespace truncation

  inductive trunc_index : Type₁ :=
  minus_two : trunc_index,
  trunc_S : trunc_index → trunc_index

  postfix `.+1`:(max+1) := trunc_index.trunc_S
  postfix `.+2`:(max+1) := λn, (n .+1 .+1)
  notation `-2` := trunc_index.minus_two
  notation `-1` := (-2.+1)

  namespace trunc_index
  definition add (n m : trunc_index) : trunc_index :=
  trunc_index.rec_on m n (λ k l, l .+1)

  definition leq (n m : trunc_index) : Type₁ :=
  trunc_index.rec_on n (λm, unit) (λ n p m, trunc_index.rec_on m (λ p, empty) (λ m q p, p m) p) m
  end trunc_index

  -- Coq calls this `-2+`, but `+2+` looks more natural, since trunc_index_add 0 0 = 2
  infix `+2+`:65 := trunc_index.add

  notation x <= y := trunc_index.leq x y
  notation x ≤ y := trunc_index.leq x y

  namespace trunc_index
  definition succ_le {n m : trunc_index} (H : n ≤ m) : n.+1 ≤ m.+1 := H
  definition succ_le_cancel {n m : trunc_index} (H : n.+1 ≤ m.+1) : n ≤ m := H
  definition minus_two_le (n : trunc_index) : -2 ≤ n := star
  definition not_succ_le_minus_two {n : trunc_index} (H : n .+1 ≤ -2) : empty := H
  end trunc_index

  definition nat_to_trunc_index [coercion] (n : nat) : trunc_index :=
  nat.rec_on n (-1.+1) (λ n k, k.+1)

  /- truncated types -/

  /-
    Just as in Coq HoTT we define an internal version of contractibility and is_trunc, but we only
    use `is_trunc` and `is_contr`
  -/

  structure contr_internal (A : Type) :=
    (center : A) (contr : Π(a : A), center = a)

  definition is_trunc_internal (n : trunc_index) : Type → Type :=
    trunc_index.rec_on n (λA, contr_internal A)
      (λn trunc_n A, (Π(x y : A), trunc_n (x = y)))

  structure is_trunc [class] (n : trunc_index) (A : Type) :=
    (to_internal : is_trunc_internal n A)

  -- should this be notation or definitions?
  notation `is_contr` := is_trunc -2
  notation `is_hprop` := is_trunc -1
  notation `is_hset`  := is_trunc (nat_to_trunc_index nat.zero)
  -- definition is_contr := is_trunc -2
  -- definition is_hprop := is_trunc -1
  -- definition is_hset  := is_trunc 0

  variables {A B : Type}

  -- TODO: rename to is_trunc_succ
  definition is_trunc_succ (A : Type) (n : trunc_index) [H : ∀x y : A, is_trunc n (x = y)]
    : is_trunc n.+1 A :=
  is_trunc.mk (λ x y, !is_trunc.to_internal)

  -- TODO: rename to is_trunc_path
  definition succ_is_trunc (n : trunc_index) [H : is_trunc (n.+1) A] (x y : A) : is_trunc n (x = y) :=
  is_trunc.mk (!is_trunc.to_internal x y)

  /- contractibility -/

  definition is_contr.mk (center : A) (contr : Π(a : A), center = a) : is_contr A :=
  is_trunc.mk (contr_internal.mk center contr)

  definition center (A : Type) [H : is_contr A] : A :=
  @contr_internal.center A !is_trunc.to_internal

  definition contr [H : is_contr A] (a : A) : !center = a :=
  @contr_internal.contr A !is_trunc.to_internal a

  definition path_contr [H : is_contr A] (x y : A) : x = y :=
  contr x⁻¹ ⬝ (contr y)

  definition path2_contr {A : Type} [H : is_contr A] {x y : A} (p q : x = y) : p = q :=
  have K : ∀ (r : x = y), path_contr x y = r, from (λ r, eq.rec_on r !concat_Vp),
  K p⁻¹ ⬝ K q

  definition contr_paths_contr [instance] {A : Type} [H : is_contr A] (x y : A) : is_contr (x = y) :=
  is_contr.mk !path_contr (λ p, !path2_contr)

  /- truncation is upward close -/

  -- n-types are also (n+1)-types
  definition trunc_succ [instance] (A : Type) (n : trunc_index) [H : is_trunc n A] : is_trunc (n.+1) A :=
  trunc_index.rec_on n
    (λ A (H : is_contr A), !is_trunc_succ)
    (λ n IH A (H : is_trunc (n.+1) A), @is_trunc_succ _ _ (λ x y, IH _ !succ_is_trunc))
    A H
  --in the proof the type of H is given explicitly to make it available for class inference


  definition trunc_leq (A : Type) (n m : trunc_index) (Hnm : n ≤ m)
    [Hn : is_trunc n A] : is_trunc m A :=
  have base : ∀k A, k ≤ -2 → is_trunc k A → (is_trunc -2 A), from
    λ k A, trunc_index.cases_on k
           (λh1 h2, h2)
           (λk h1 h2, empty.elim (is_trunc -2 A) (trunc_index.not_succ_le_minus_two h1)),
  have step : Π (m : trunc_index)
                (IHm : Π (n : trunc_index) (A : Type), n ≤ m → is_trunc n A → is_trunc m A)
                (n : trunc_index) (A : Type)
                (Hnm : n ≤ m .+1) (Hn : is_trunc n A), is_trunc m .+1 A, from
    λm IHm n, trunc_index.rec_on n
           (λA Hnm Hn, @trunc_succ A m (IHm -2 A star Hn))
           (λn IHn A Hnm (Hn : is_trunc n.+1 A),
           @is_trunc_succ A m (λx y, IHm n (x = y) (trunc_index.succ_le_cancel Hnm) !succ_is_trunc)),
  trunc_index.rec_on m base step n A Hnm Hn

  -- the following cannot be instances in their current form, because it is looping
  definition trunc_contr (A : Type) (n : trunc_index) [H : is_contr A] : is_trunc n A :=
  trunc_index.rec_on n H _

  definition trunc_hprop (A : Type) (n : trunc_index) [H : is_hprop A]
      : is_trunc (n.+1) A :=
  trunc_leq A -1 (n.+1) star

  definition trunc_hset (A : Type) (n : trunc_index) [H : is_hset A]
      : is_trunc (n.+2) A :=
  trunc_leq A nat.zero (n.+2) star

  /- hprops -/

  definition is_hprop.elim [H : is_hprop A] (x y : A) : x = y :=
  @center _ !succ_is_trunc

  definition contr_inhabited_hprop {A : Type} [H : is_hprop A] (x : A) : is_contr A :=
  is_contr.mk x (λy, !is_hprop.elim)

  --Coq has the following as instance, but doesn't look too useful
  definition hprop_inhabited_contr {A : Type} (H : A → is_contr A) : is_hprop A :=
  @is_trunc_succ A -2
    (λx y,
      have H2 [visible] : is_contr A, from H x,
      !contr_paths_contr)

  definition is_hprop.mk {A : Type} (H : ∀x y : A, x = y) : is_hprop A :=
  hprop_inhabited_contr (λ x, is_contr.mk x (H x))

  /- hsets -/

  definition is_hset.mk (A : Type) (H : ∀(x y : A) (p q : x = y), p = q) : is_hset A :=
  @is_trunc_succ _ _ (λ x y, is_hprop.mk (H x y))

  definition is_hset.elim [H : is_hset A] ⦃x y : A⦄ (p q : x = y) : p = q :=
  @is_hprop.elim _ !succ_is_trunc p q

  /- instances -/

  definition contr_basedpaths [instance] {A : Type} (a : A) : is_contr (Σ(x : A), a = x) :=
  is_contr.mk (dpair a idp) (λp, sigma.rec_on p (λ b q, eq.rec_on q idp))

  -- definition is_trunc_is_hprop [instance] {n : trunc_index} : is_hprop (is_trunc n A) := sorry

  definition unit_contr [instance] : is_contr unit :=
  is_contr.mk star (λp, unit.rec_on p idp)

  definition empty_hprop [instance] : is_hprop empty :=
  is_hprop.mk (λx, !empty.elim x)

  /- truncated universe -/

  structure trunctype (n : trunc_index) :=
  (trunctype_type : Type) (is_trunc_trunctype_type : is_trunc n trunctype_type)
  coercion trunctype.trunctype_type

  notation n `-Type` := trunctype n
  notation `hprop` := -1-Type
  notation `hset` := 0-Type

  definition hprop.mk := @trunctype.mk -1
  definition hset.mk := @trunctype.mk nat.zero

  --what does the following line in Coq do?
  --Canonical Structure default_TruncType := fun n T P => (@BuildTruncType n T P).

  /- interaction with equivalences -/

  section
  open is_equiv equiv

  --should we remove the following two theorems as they are special cases of "trunc_equiv"
  definition equiv_preserves_contr (f : A → B) [Hf : is_equiv f] [HA: is_contr A] : (is_contr B) :=
    is_contr.mk (f (center A)) (λp, moveR_M f !contr)

  theorem contr_equiv (H : A ≃ B) [HA: is_contr A] : is_contr B :=
    @equiv_preserves_contr _ _ (to_fun H) (to_is_equiv H) _

  definition contr_equiv_contr [HA : is_contr A] [HB : is_contr B] : A ≃ B :=
  equiv.mk
    (λa, center B)
    (is_equiv.adjointify (λa, center B) (λb, center A) contr contr)

  definition trunc_equiv (n : trunc_index) (f : A → B) [H : is_equiv f] [HA : is_trunc n A]
      : is_trunc n B :=
  trunc_index.rec_on n
    (λA (HA : is_contr A) B f (H : is_equiv f), !equiv_preserves_contr)
    (λn IH A (HA : is_trunc n.+1 A) B f (H : is_equiv f), @is_trunc_succ _ _ (λ x y : B,
      IH (f⁻¹ x = f⁻¹ y) !succ_is_trunc (x = y) ((ap (f⁻¹))⁻¹) !inv_closed))
    A HA B f H

  definition trunc_equiv' (n : trunc_index) (f : A ≃ B) [HA : is_trunc n A] : is_trunc n B :=
  trunc_equiv n (to_fun f)

  definition isequiv_iff_hprop [HA : is_hprop A] [HB : is_hprop B] (f : A → B) (g : B → A)
      : is_equiv f :=
  is_equiv.adjointify f g (λb, !is_hprop.elim) (λa, !is_hprop.elim)

  -- definition equiv_iff_hprop_uncurried [HA : is_hprop A] [HB : is_hprop B] : (A ↔ B) → (A ≃ B)  := sorry

  definition equiv_iff_hprop [HA : is_hprop A] [HB : is_hprop B] (f : A → B) (g : B → A) : A ≃ B :=
  equiv.mk f (isequiv_iff_hprop f g)
  end

  /- interaction with the Unit type -/

  -- A contractible type is equivalent to [Unit]. *)
  definition equiv_contr_unit [H : is_contr A] : A ≃ unit :=
    equiv.mk (λ (x : A), ⋆)
      (is_equiv.mk (λ (u : unit), center A)
        (λ (u : unit), unit.rec_on u idp)
        (λ (x : A), contr x)
        (λ (x : A), (!ap_const)⁻¹))

  -- TODO: port "Truncated morphisms"

end truncation
