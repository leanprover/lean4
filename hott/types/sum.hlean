/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Theorems about sums/coproducts/disjoint unions
-/

import .pi .equiv logic

open lift eq is_equiv equiv equiv.ops prod prod.ops is_trunc sigma bool

namespace sum
  universe variables u v u' v'
  variables {A : Type.{u}} {B : Type.{v}} (z z' : A + B) {P : A → Type.{u'}} {Q : A → Type.{v'}}

  protected definition eta : sum.rec inl inr z = z :=
  by induction z; all_goals reflexivity

  protected definition code [unfold 3 4] : A + B → A + B → Type.{max u v}
  | code (inl a) (inl a') := lift (a = a')
  | code (inr b) (inr b') := lift (b = b')
  | code _       _        := lift empty

  protected definition decode [unfold 3 4] : Π(z z' : A + B), sum.code z z' → z = z'
  | decode (inl a) (inl a') := λc, ap inl (down c)
  | decode (inl a) (inr b') := λc, empty.elim (down c) _
  | decode (inr b) (inl a') := λc, empty.elim (down c) _
  | decode (inr b) (inr b') := λc, ap inr (down c)

  protected definition mem_cases : (Σ a, z = inl a) + (Σ b, z = inr b) :=
  by cases z with a b; exact inl ⟨a, idp⟩; exact inr ⟨b, idp⟩

  protected definition eqrec {A B : Type} {C : A + B → Type}
    (x : A + B) (cl : Π a, x = inl a → C (inl a)) (cr : Π b, x = inr b → C (inr b)) : C x :=
  by cases x with a b; exact cl a idp; exact cr b idp

  variables {z z'}
  protected definition encode [unfold 3 4 5] (p : z = z') : sum.code z z' :=
  by induction p; induction z; all_goals exact up idp

  variables (z z')
  definition sum_eq_equiv [constructor] : (z = z') ≃ sum.code z z' :=
  equiv.MK sum.encode
           !sum.decode
           abstract begin
             intro c, induction z with a b, all_goals induction z' with a' b',
             all_goals (esimp at *; induction c with c),
             all_goals induction c, -- c either has type empty or a path
             all_goals reflexivity
           end end
           abstract begin
             intro p, induction p, induction z, all_goals reflexivity
           end end

  section
  variables {a a' : A} {b b' : B}
  definition eq_of_inl_eq_inl [unfold 5] (p : inl a = inl a' :> A + B) : a = a' :=
  down (sum.encode p)
  definition eq_of_inr_eq_inr [unfold 5] (p : inr b = inr b' :> A + B) : b = b' :=
  down (sum.encode p)
  definition empty_of_inl_eq_inr (p : inl a = inr b) : empty := down (sum.encode p)
  definition empty_of_inr_eq_inl (p : inr b = inl a) : empty := down (sum.encode p)

  /- Transport -/

  definition sum_transport (p : a = a') (z : P a + Q a)
    : p ▸ z = sum.rec (λa, inl (p ▸ a)) (λb, inr (p ▸ b)) z :=
  by induction p; induction z; all_goals reflexivity

  /- Pathovers -/

  definition etao (p : a = a') (z : P a + Q a)
    : z =[p] sum.rec (λa, inl (p ▸ a)) (λb, inr (p ▸ b)) z :=
  by induction p; induction z; all_goals constructor

  protected definition codeo (p : a = a') : P a + Q a → P a' + Q a' → Type.{max u' v'}
  | codeo (inl x) (inl x') := lift.{u' v'} (x =[p] x')
  | codeo (inr y) (inr y') := lift.{v' u'} (y =[p] y')
  | codeo _       _        := lift empty

  protected definition decodeo (p : a = a') : Π(z : P a + Q a) (z' : P a' + Q a'),
    sum.codeo p z z' → z =[p] z'
  | decodeo (inl x) (inl x') := λc, apo (λa, inl) (down c)
  | decodeo (inl x) (inr y') := λc, empty.elim (down c) _
  | decodeo (inr y) (inl x') := λc, empty.elim (down c) _
  | decodeo (inr y) (inr y') := λc, apo (λa, inr) (down c)

  variables {z z'}
  protected definition encodeo {p : a = a'} {z : P a + Q a} {z' : P a' + Q a'} (q : z =[p] z')
    : sum.codeo p z z' :=
  by induction q; induction z; all_goals exact up idpo

  variables (z z')
  definition sum_pathover_equiv [constructor] (p : a = a') (z : P a + Q a) (z' : P a' + Q a')
    : (z =[p] z') ≃ sum.codeo p z z' :=
  equiv.MK sum.encodeo
           !sum.decodeo
           abstract begin
             intro c, induction z with a b, all_goals induction z' with a' b',
             all_goals (esimp at *; induction c with c),
             all_goals induction c, -- c either has type empty or a pathover
             all_goals reflexivity
           end end
           abstract begin
             intro q, induction q, induction z, all_goals reflexivity
           end end
  end

  /- Functorial action -/

  variables {A' B' : Type} (f : A → A') (g : B → B')
  definition sum_functor [unfold 7] : A + B → A' + B'
  | sum_functor (inl a) := inl (f a)
  | sum_functor (inr b) := inr (g b)

  /- Equivalences -/

  definition is_equiv_sum_functor [constructor] [Hf : is_equiv f] [Hg : is_equiv g]
    : is_equiv (sum_functor f g) :=
  adjointify (sum_functor f   g)
             (sum_functor f⁻¹ g⁻¹)
             abstract begin
               intro z, induction z,
               all_goals (esimp; (apply ap inl | apply ap inr); apply right_inv)
             end end
             abstract begin
               intro z, induction z,
               all_goals (esimp; (apply ap inl | apply ap inr); apply right_inv)
             end end

  definition sum_equiv_sum_of_is_equiv [constructor] [Hf : is_equiv f] [Hg : is_equiv g]
    : A + B ≃ A' + B' :=
  equiv.mk _ (is_equiv_sum_functor f g)

  definition sum_equiv_sum [constructor] (f : A ≃ A') (g : B ≃ B') : A + B ≃ A' + B' :=
  equiv.mk _ (is_equiv_sum_functor f g)

  definition sum_equiv_sum_left [constructor] (g : B ≃ B') : A + B ≃ A + B' :=
  sum_equiv_sum equiv.refl g

  definition sum_equiv_sum_right [constructor] (f : A ≃ A') : A + B ≃ A' + B :=
  sum_equiv_sum f equiv.refl

  definition flip [unfold 3] : A + B → B + A
  | flip (inl a) := inr a
  | flip (inr b) := inl b

  definition sum_comm_equiv [constructor] (A B : Type) : A + B ≃ B + A :=
  begin
    fapply equiv.MK,
      exact flip,
      exact flip,
      all_goals (intro z; induction z; all_goals reflexivity)
  end

  definition sum_assoc_equiv [constructor] (A B C : Type) : A + (B + C) ≃ (A + B) + C :=
  begin
    fapply equiv.MK,
      all_goals try (intro z; induction z with u v;
                     all_goals try induction u; all_goals try induction v),
      all_goals try (repeat append (append (apply inl) (apply inr)) assumption; now),
      all_goals reflexivity
  end

  definition sum_empty_equiv [constructor] (A : Type) : A + empty ≃ A :=
  begin
    fapply equiv.MK,
    { intro z, induction z, assumption, contradiction},
    { exact inl},
    { intro a, reflexivity},
    { intro z, induction z, reflexivity, contradiction}
  end

  definition empty_sum_equiv (A : Type) : empty + A ≃ A :=
  !sum_comm_equiv ⬝e !sum_empty_equiv

  definition bool_equiv_unit_sum_unit : bool ≃ unit + unit :=
  begin
    fapply equiv.MK,
    { intro b, cases b, exact inl unit.star, exact inr unit.star },
    { intro s, cases s, exact bool.ff, exact bool.tt },
    { intro s, cases s, do 2 (cases a; reflexivity) },
    { intro b, cases b, do 2 reflexivity },
  end

  definition sum_prod_right_distrib [constructor] (A B C : Type) :
    (A + B) × C ≃ (A × C) + (B × C) :=
  begin
    fapply equiv.MK,
    { intro x, cases x with ab c, cases ab with a b, exact inl (a, c), exact inr (b, c) },
    { intro x, cases x with ac bc, cases ac with a c, exact (inl a, c),  
      cases bc with b c, exact (inr b, c) },
    { intro x, cases x with ac bc, cases ac with a c, reflexivity, cases bc, reflexivity },
    { intro x, cases x with ab c, cases ab with a b, do 2 reflexivity }
  end

  definition sum_prod_left_distrib [constructor] (A B C : Type) :
    A × (B + C) ≃ (A × B) + (A × C) :=
  calc A × (B + C) ≃ (B + C) × A : prod_comm_equiv
               ... ≃ (B × A) + (C × A) : sum_prod_right_distrib
               ... ≃ (A × B) + (C × A) : prod_comm_equiv
               ... ≃ (A × B) + (A × C) : prod_comm_equiv

  section
  variables (H : unit + A ≃ unit + B)
  include H  

  open unit decidable sigma.ops

  definition unit_sum_equiv_cancel_map : A → B :=
  begin
    intro a, cases sum.mem_cases (H (inr a)) with u b, rotate 1, exact b.1,
    cases u with u Hu, cases sum.mem_cases (H (inl ⋆)) with u' b, rotate 1, exact b.1,
    cases u' with u' Hu', exfalso, apply empty_of_inl_eq_inr,
    calc inl ⋆ = H⁻¹ (H (inl ⋆)) : (to_left_inv H (inl ⋆))⁻¹
           ... = H⁻¹ (inl u') : {Hu'}
           ... = H⁻¹ (inl u) : is_hprop.elim
           ... = H⁻¹ (H (inr a)) : {Hu⁻¹}
           ... = inr a : to_left_inv H (inr a)
  end

  definition unit_sum_equiv_cancel_inv (b : B) :
    unit_sum_equiv_cancel_map H (unit_sum_equiv_cancel_map H⁻¹ b) = b :=
  begin
    assert HH : to_fun H⁻¹ = (to_fun H)⁻¹, cases H, reflexivity,
    esimp[unit_sum_equiv_cancel_map], apply sum.rec,
    { intro x, cases x with u Hu, esimp, apply sum.rec,
      { intro x, exfalso, cases x with u' Hu', apply empty_of_inl_eq_inr,
        calc inl ⋆ = H⁻¹ (H (inl ⋆)) : (to_left_inv H (inl ⋆))⁻¹
               ... = H⁻¹ (inl u') : ap H⁻¹ Hu'
               ... = H⁻¹ (inl u) : {!is_hprop.elim}
               ... = H⁻¹ (H (inr _)) : {Hu⁻¹}
               ... = inr _ : to_left_inv H },
      { intro x, cases x with b' Hb', esimp, cases sum.mem_cases (H⁻¹ (inr b)) with x x,
        { cases x with u' Hu', cases u', apply eq_of_inr_eq_inr, rewrite -HH at Hu',
          calc inr b' = H (inl ⋆) : Hb'⁻¹
                  ... = H (H⁻¹ (inr b)) : {(ap (to_fun H) Hu')⁻¹}
                  ... = inr b : to_right_inv H (inr b) },
        { exfalso, cases x with a Ha, rewrite -HH at Ha, apply empty_of_inl_eq_inr,
          cases u, apply concat, apply Hu⁻¹, apply concat, rotate 1, apply !(to_right_inv H),
          apply ap (to_fun H), krewrite -HH,
          apply concat, rotate 1, apply Ha⁻¹, apply ap inr, esimp,
          apply sum.rec, intro x, exfalso, apply empty_of_inl_eq_inr,
          apply concat, exact x.2⁻¹, apply Ha,
          intro x, cases x with a' Ha', esimp, apply eq_of_inr_eq_inr, apply Ha'⁻¹ ⬝ Ha } } },
    { intro x, cases x with b' Hb', esimp, apply eq_of_inr_eq_inr, refine Hb'⁻¹ ⬝ _, 
      cases sum.mem_cases (to_fun H⁻¹ (inr b)) with x x,
      { cases x with u Hu, esimp, cases sum.mem_cases (to_fun H⁻¹ (inl ⋆)) with x x, 
        { cases x with u' Hu', exfalso, apply empty_of_inl_eq_inr, 
          calc inl ⋆ = H (H⁻¹ (inl ⋆)) : (to_right_inv H (inl ⋆))⁻¹
                 ... = H (inl u') : {ap H Hu'}
                 ... = H (inl u) : {!is_hprop.elim}
                 ... = H (H⁻¹ (inr b)) : {ap H Hu⁻¹}
                 ... = inr b : to_right_inv H (inr b) },
      { cases x with a Ha, exfalso, apply empty_of_inl_eq_inr, 
        apply concat, rotate 1, exact Hb', krewrite HH at Ha,
        assert Ha' : inl ⋆ = H (inr a), apply !(to_right_inv H)⁻¹ ⬝ ap H Ha, 
        apply concat Ha', apply ap H, apply ap inr, apply sum.rec,
          intro x, cases x with u' Hu', esimp, apply sum.rec,
            intro x, cases x with u'' Hu'', esimp, apply empty.rec,
            intro x, cases x with a'' Ha'', esimp, krewrite Ha' at Ha'', apply eq_of_inr_eq_inr,
            apply !(to_left_inv H)⁻¹ ⬝ Ha'', 
          intro x, exfalso, cases x with a'' Ha'', apply empty_of_inl_eq_inr,
          apply Hu⁻¹ ⬝ Ha'', } },
    { cases x with a' Ha', esimp, refine _ ⬝ !(to_right_inv H), apply ap H, 
      rewrite -HH, apply Ha'⁻¹ } }
  end

  definition unit_sum_equiv_cancel : A ≃ B :=
  begin
    fapply equiv.MK, apply unit_sum_equiv_cancel_map H,
    apply unit_sum_equiv_cancel_map H⁻¹,
    intro b, apply unit_sum_equiv_cancel_inv,
    { intro a, have H = (H⁻¹)⁻¹, from !equiv.symm_symm⁻¹, rewrite this at {2}, 
      apply unit_sum_equiv_cancel_inv }
  end

  end

  /- universal property -/

  definition sum_rec_unc [unfold 5] {P : A + B → Type} (fg : (Πa, P (inl a)) × (Πb, P (inr b)))
    : Πz, P z :=
  sum.rec fg.1 fg.2

  definition is_equiv_sum_rec [constructor] (P : A + B → Type)
    : is_equiv (sum_rec_unc : (Πa, P (inl a)) × (Πb, P (inr b)) → Πz, P z) :=
  begin
     apply adjointify sum_rec_unc (λf, (λa, f (inl a), λb, f (inr b))),
       intro f, apply eq_of_homotopy, intro z, focus (induction z; all_goals reflexivity),
       intro h, induction h with f g, reflexivity
  end

  definition equiv_sum_rec [constructor] (P : A + B → Type)
    : (Πa, P (inl a)) × (Πb, P (inr b)) ≃ Πz, P z :=
  equiv.mk _ !is_equiv_sum_rec

  definition imp_prod_imp_equiv_sum_imp [constructor] (A B C : Type)
    : (A → C) × (B → C) ≃ (A + B → C) :=
  !equiv_sum_rec

  /- truncatedness -/

  variables (A B)
  theorem is_trunc_sum (n : trunc_index) [HA : is_trunc (n.+2) A]  [HB : is_trunc (n.+2) B]
    : is_trunc (n.+2) (A + B) :=
  begin
    apply is_trunc_succ_intro, intro z z',
    apply is_trunc_equiv_closed_rev, apply sum_eq_equiv,
    induction z with a b, all_goals induction z' with a' b', all_goals esimp,
    all_goals exact _,
  end

  theorem is_trunc_sum_excluded (n : trunc_index) [HA : is_trunc n A]  [HB : is_trunc n B]
    (H : A → B → empty) : is_trunc n (A + B) :=
  begin
    induction n with n IH,
    { exfalso, exact H !center !center},
    { clear IH, induction n with n IH,
      { apply is_hprop.mk, intros x y,
        induction x, all_goals induction y, all_goals esimp,
        all_goals try (exfalso;apply H;assumption;assumption), all_goals apply ap _ !is_hprop.elim},
      { apply is_trunc_sum}}
  end

  variable {B}
  definition is_contr_sum_left [HA : is_contr A] (H : ¬B) : is_contr (A + B) :=
  is_contr.mk (inl !center)
              (λx, sum.rec_on x (λa, ap inl !center_eq) (λb, empty.elim (H b)))

  /-
    Sums are equivalent to dependent sigmas where the first component is a bool.

    The current construction only works for A and B in the same universe.
    If we need it for A and B in different universes, we need to insert some lifts.
  -/

  definition sum_of_sigma_bool {A B : Type.{u}} (v : Σ(b : bool), bool.rec A B b) : A + B :=
  by induction v with b x; induction b; exact inl x; exact inr x

  definition sigma_bool_of_sum {A B : Type.{u}} (z : A + B) : Σ(b : bool), bool.rec A B b :=
  by induction z with a b; exact ⟨ff, a⟩; exact ⟨tt, b⟩

  definition sum_equiv_sigma_bool [constructor] (A B : Type.{u})
    : A + B ≃ Σ(b : bool), bool.rec A B b :=
  equiv.MK sigma_bool_of_sum
           sum_of_sigma_bool
           begin intro v, induction v with b x, induction b, all_goals reflexivity end
           begin intro z, induction z with a b, all_goals reflexivity end

end sum
open sum pi

namespace decidable

  definition decidable_equiv [constructor] (A : Type) : decidable A ≃ A + ¬A :=
  begin
    fapply equiv.MK:intro a;induction a:try (constructor;assumption;now),
    all_goals reflexivity
  end

  definition is_trunc_decidable [constructor] (A : Type) (n : trunc_index) [H : is_trunc n A] :
    is_trunc n (decidable A) :=
  begin
    apply is_trunc_equiv_closed_rev,
    apply decidable_equiv,
    induction n with n IH,
    { apply is_contr_sum_left, exact λna, na !center},
    { apply is_trunc_sum_excluded, exact λa na, na a}
  end

end decidable

attribute sum.is_trunc_sum [instance] [priority 1480]

definition tsum [constructor] {n : trunc_index} (A B : (n.+2)-Type) : (n.+2)-Type :=
trunctype.mk (A + B) _

infixr `+t`:25 := tsum
