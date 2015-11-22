/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Declaration of set-quotients, i.e. quotient of a mere relation which is then set-truncated.
-/

import function algebra.relation types.trunc types.eq

open eq is_trunc trunc quotient equiv

namespace set_quotient
section
  parameters {A : Type} (R : A → A → hprop)
  -- set-quotients are just truncations of (type) quotients
  definition set_quotient : Type := trunc 0 (quotient (λa a', trunctype.carrier (R a a')))

  parameter {R}
  definition class_of (a : A) : set_quotient :=
  tr (class_of _ a)

  definition eq_of_rel {a a' : A} (H : R a a') : class_of a = class_of a' :=
  ap tr (eq_of_rel _ H)

  theorem is_hset_set_quotient [instance] : is_hset set_quotient :=
  begin unfold set_quotient, exact _ end

  protected definition rec {P : set_quotient → Type} [Pt : Πaa, is_hset (P aa)]
    (Pc : Π(a : A), P (class_of a)) (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a =[eq_of_rel H] Pc a')
    (x : set_quotient) : P x :=
  begin
    apply (@trunc.rec_on _ _ P x),
    { intro x', apply Pt},
    { intro y, fapply (quotient.rec_on y),
      { exact Pc},
      { intros, exact pathover_of_pathover_ap P tr (Pp H)}}
  end

  protected definition rec_on [reducible] {P : set_quotient → Type} (x : set_quotient)
    [Pt : Πaa, is_hset (P aa)] (Pc : Π(a : A), P (class_of a))
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a =[eq_of_rel H] Pc a') : P x :=
  rec Pc Pp x

  theorem rec_eq_of_rel {P : set_quotient → Type} [Pt : Πaa, is_hset (P aa)]
    (Pc : Π(a : A), P (class_of a)) (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a =[eq_of_rel H] Pc a')
    {a a' : A} (H : R a a') : apdo (rec Pc Pp) (eq_of_rel H) = Pp H :=
  !is_hset.elimo

  protected definition elim {P : Type} [Pt : is_hset P] (Pc : A → P)
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a = Pc a') (x : set_quotient) : P :=
  rec Pc (λa a' H, pathover_of_eq (Pp H)) x

  protected definition elim_on [reducible] {P : Type} (x : set_quotient) [Pt : is_hset P]
    (Pc : A → P) (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a = Pc a')  : P :=
  elim Pc Pp x

  theorem elim_eq_of_rel {P : Type} [Pt : is_hset P] (Pc : A → P)
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a = Pc a') {a a' : A} (H : R a a')
    : ap (elim Pc Pp) (eq_of_rel H) = Pp H :=
  begin
    apply eq_of_fn_eq_fn_inv !(pathover_constant (eq_of_rel H)),
    rewrite [▸*,-apdo_eq_pathover_of_eq_ap,↑elim,rec_eq_of_rel],
  end

  protected definition rec_hprop {P : set_quotient → Type} [Pt : Πaa, is_hprop (P aa)]
    (Pc : Π(a : A), P (class_of a)) (x : set_quotient) : P x :=
  rec Pc (λa a' H, !is_hprop.elimo) x

  protected definition elim_hprop {P : Type} [Pt : is_hprop P] (Pc : A → P) (x : set_quotient)
    : P :=
  elim Pc (λa a' H, !is_hprop.elim) x

  /-
    there are no theorems to eliminate to the universe here,
    because the universe is generally not a set
  -/

end
end set_quotient

attribute set_quotient.class_of [constructor]
attribute set_quotient.rec set_quotient.elim [unfold 7] [recursor 7]
attribute set_quotient.rec_on set_quotient.elim_on [unfold 4]

open sigma relation function

namespace set_quotient
  variables {A B C : Type} (R : A → A → hprop) (S : B → B → hprop) (T : C → C → hprop)

  definition is_surjective_class_of : is_surjective (class_of : A → set_quotient R) :=
  λx, set_quotient.rec_on x (λa, tr (fiber.mk a idp)) (λa a' r, !is_hprop.elimo)

  /- non-dependent universal property -/

  definition set_quotient_arrow_equiv (B : Type) [H : is_hset B] :
    (set_quotient R → B) ≃ (Σ(f : A → B), Π(a a' : A), R a a' → f a = f a') :=
  begin
    fapply equiv.MK,
    { intro f, exact ⟨λa, f (class_of a), λa a' r, ap f (eq_of_rel r)⟩},
    { intro v x, induction v with f p, exact set_quotient.elim_on x f p},
    { intro v, induction v with f p, esimp, apply ap (sigma.mk f),
      apply eq_of_homotopy3, intro a a' r, apply elim_eq_of_rel},
    { intro f, apply eq_of_homotopy, intro x, refine set_quotient.rec_on x _ _: esimp,
        intro a, reflexivity,
        intro a a' r, apply eq_pathover, apply hdeg_square, apply elim_eq_of_rel}
  end

  protected definition code [unfold 4] (a : A) (x : set_quotient R) [H : is_equivalence R]
    : hprop :=
  set_quotient.elim_on x (R a)
    begin
      intros a' a'' H1,
      refine to_inv !trunctype_eq_equiv _, esimp,
      apply ua,
      apply equiv_of_is_hprop,
      { intro H2, exact is_transitive.trans R H2 H1},
      { intro H2, apply is_transitive.trans R H2, exact is_symmetric.symm R H1}
    end

  protected definition encode {a : A} {x : set_quotient R} (p : class_of a = x)
    [H : is_equivalence R] : set_quotient.code R a x :=
  begin
    induction p, esimp, apply is_reflexive.refl R
  end

  definition rel_of_eq {a a' : A} (p : class_of a = class_of a' :> set_quotient R)
    [H : is_equivalence R] : R a a' :=
  set_quotient.encode R p

  variables {R S T}
  definition quotient_unary_map [unfold 7] (f : A → B) (H : Π{a a'} (r : R a a'), S (f a) (f a')) :
    set_quotient R → set_quotient S :=
  set_quotient.elim (class_of ∘ f) (λa a' r, eq_of_rel (H r))

  definition quotient_binary_map [unfold 10 11] (f : A → B → C)
    (H : Π{a a'} (r : R a a') {b b'} (s : S b b'), T (f a b) (f a' b'))
    [HR : is_reflexive R] [HS : is_reflexive S] :
    set_quotient R → set_quotient S → set_quotient T :=
  begin
    refine set_quotient.elim _ _,
    { intro a, refine set_quotient.elim _ _,
      { intro b, exact class_of (f a b)},
      { intro b b' s, apply eq_of_rel, apply H, apply is_reflexive.refl R, exact s}},
    { intro a a' r, apply eq_of_homotopy, refine set_quotient.rec _ _,
      { intro b, esimp, apply eq_of_rel, apply H, exact r, apply is_reflexive.refl S},
      { intro b b' s, apply eq_pathover, esimp, apply is_hset.elims}}
  end

end set_quotient
