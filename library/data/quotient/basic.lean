/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

An explicit treatment of quotients, without using Lean's built-in quotient types.
-/
import logic logic.cast algebra.relation data.prod
import logic.instances
import .util

open relation prod inhabited nonempty tactic eq.ops
open subtype relation.iff_ops

namespace quotient

/- definition and basics -/

-- TODO: make this a structure
definition is_quotient {A B : Type} (R : A → A → Prop) (abs : A → B) (rep : B → A) : Prop :=
  (∀b, abs (rep b) = b) ∧
  (∀b, R (rep b) (rep b)) ∧
  (∀r s, R r s ↔ (R r r ∧ R s s ∧ abs r = abs s))

theorem intro {A B : Type} {R : A → A → Prop} {abs : A → B} {rep : B → A}
  (H1 : ∀b, abs (rep b) = b) (H2 : ∀b, R (rep b) (rep b))
  (H3 : ∀r s, R r s ↔ (R r r ∧ R s s ∧ abs r = abs s)) : is_quotient R abs rep :=
and.intro H1 (and.intro H2 H3)

theorem and_absorb_left {a : Prop} (b : Prop) (Ha : a) : a ∧ b ↔ b :=
iff.intro (assume Hab, and.elim_right Hab) (assume Hb, and.intro Ha Hb)

theorem intro_refl {A B : Type} {R : A → A → Prop} {abs : A → B} {rep : B → A}
  (H1 : reflexive R) (H2 : ∀b, abs (rep b) = b)
  (H3 : ∀r s, R r s ↔ abs r = abs s) : is_quotient R abs rep :=
intro
  H2
  (take b, H1 (rep b))
  (take r s,
    have H4 : R r s ↔ R s s ∧ abs r = abs s,
      from
        subst (symm (and_absorb_left _ (H1 s))) (H3 r s),
    subst (symm (and_absorb_left _ (H1 r))) H4)

theorem abs_rep {A B : Type} {R : A → A → Prop} {abs : A → B} {rep : B → A}
  (Q : is_quotient R abs rep) (b : B) :  abs (rep b) = b :=
and.elim_left Q b

theorem refl_rep {A B : Type} {R : A → A → Prop} {abs : A → B} {rep : B → A}
  (Q : is_quotient R abs rep) (b : B) : R (rep b) (rep b) :=
and.elim_left (and.elim_right Q) b

theorem R_iff {A B : Type} {R : A → A → Prop} {abs : A → B} {rep : B → A}
  (Q : is_quotient R abs rep) (r s : A) : R r s ↔ (R r r ∧ R s s ∧ abs r = abs s) :=
and.elim_right (and.elim_right Q) r s

theorem refl_left {A B : Type} {R : A → A → Prop} {abs : A → B} {rep : B → A}
  (Q : is_quotient R abs rep) {r s : A} (H : R r s) : R r r :=
and.elim_left (iff.elim_left (R_iff Q r s) H)

theorem refl_right {A B : Type} {R : A → A → Prop} {abs : A → B} {rep : B → A}
  (Q : is_quotient R abs rep) {r s : A} (H : R r s) : R s s :=
and.elim_left (and.elim_right (iff.elim_left (R_iff Q r s) H))

theorem eq_abs {A B : Type} {R : A → A → Prop} {abs : A → B} {rep : B → A}
  (Q : is_quotient R abs rep) {r s : A} (H : R r s) : abs r = abs s :=
and.elim_right (and.elim_right (iff.elim_left (R_iff Q r s) H))

theorem R_intro {A B : Type} {R : A → A → Prop} {abs : A → B} {rep : B → A}
  (Q : is_quotient R abs rep) {r s : A} (H1 : R r r) (H2 : R s s) (H3 : abs r = abs s) : R r s :=
iff.elim_right (R_iff Q r s) (and.intro H1 (and.intro H2 H3))

theorem R_intro_refl {A B : Type} {R : A → A → Prop} {abs : A → B} {rep : B → A}
  (Q : is_quotient R abs rep) (H1 : reflexive R) {r s : A} (H2 : abs r = abs s) : R r s :=
iff.elim_right (R_iff Q r s) (and.intro (H1 r) (and.intro (H1 s) H2))

theorem rep_eq {A B : Type} {R : A → A → Prop} {abs : A → B} {rep : B → A}
  (Q : is_quotient R abs rep) {a b : B} (H : R (rep a) (rep b)) : a = b :=
calc
  a = abs (rep a) : eq.symm (abs_rep Q a)
    ... = abs (rep b) : {eq_abs Q H}
    ... = b : abs_rep Q b

theorem R_rep_abs {A B : Type} {R : A → A → Prop} {abs : A → B} {rep : B → A}
  (Q : is_quotient R abs rep) {a : A} (H : R a a) : R a (rep (abs a)) :=
have H3 : abs a = abs (rep (abs a)), from eq.symm (abs_rep Q (abs a)),
R_intro Q H (refl_rep Q (abs a)) H3

theorem quotient_imp_symm {A B : Type} {R : A → A → Prop} {abs : A → B} {rep : B → A}
  (Q : is_quotient R abs rep) : symmetric R :=
take a b : A,
assume H : R a b,
have Ha : R a a, from refl_left Q H,
have Hb : R b b, from refl_right Q H,
have Hab : abs b = abs a, from eq.symm (eq_abs Q H),
R_intro Q Hb Ha Hab

theorem quotient_imp_trans {A B : Type} {R : A → A → Prop} {abs : A → B} {rep : B → A}
  (Q : is_quotient R abs rep) : transitive R :=
take a b c : A,
assume Hab : R a b,
assume Hbc : R b c,
have Ha : R a a, from refl_left Q Hab,
have Hc : R c c, from refl_right Q Hbc,
have Hac : abs a = abs c, from eq.trans (eq_abs Q Hab) (eq_abs Q Hbc),
R_intro Q Ha Hc Hac

/- recursion -/

-- (maybe some are superfluous)

definition rec {A B : Type} {R : A → A → Prop} {abs : A → B} {rep : B → A}
  (Q : is_quotient R abs rep) {C : B → Type} (f : forall (a : A), C (abs a)) (b : B) : C b :=
eq.rec_on (abs_rep Q b) (f (rep b))

theorem comp {A B : Type} {R : A → A → Prop} {abs : A → B} {rep : B → A}
  (Q : is_quotient R abs rep) {C : B → Type} {f : forall (a : A), C (abs a)}
  (H : forall (r s : A) (H' : R r s), eq.rec_on (eq_abs Q H') (f r) = f s)
  {a : A} (Ha : R a a) : rec Q f (abs a) = f a :=
assert H2  : R a (rep (abs a)), from
  R_rep_abs Q Ha,
assert Heq : abs (rep (abs a)) = abs a, from
  abs_rep Q (abs a),
calc
  rec Q f (abs a) =  eq.rec_on Heq (f (rep (abs a))) : rfl
    ... = eq.rec_on Heq (eq.rec_on (Heq⁻¹) (f a))   : {(H _ _ H2)⁻¹}
    ... = f a                                         : eq.rec_on_compose (eq_abs Q H2) _ _

definition rec_constant {A B : Type} {R : A → A → Prop} {abs : A → B} {rep : B → A}
  (Q : is_quotient R abs rep) {C : Type} (f : A → C) (b : B) : C :=
f (rep b)

theorem comp_constant {A B : Type} {R : A → A → Prop} {abs : A → B} {rep : B → A}
  (Q : is_quotient R abs rep) {C : Type} {f : A → C}
  (H : forall (r s : A) (H' : R r s), f r = f s)
  {a : A} (Ha : R a a) : rec_constant Q f (abs a) = f a :=
have H2 : R a (rep (abs a)), from R_rep_abs Q Ha,
calc
  rec_constant Q f (abs a) = f (rep (abs a)) : rfl
    ... = f a : {(H _ _ H2)⁻¹}

definition rec_binary {A B : Type} {R : A → A → Prop} {abs : A → B} {rep : B → A}
  (Q : is_quotient R abs rep) {C : Type} (f : A → A → C) (b c : B) : C :=
f (rep b) (rep c)

theorem comp_binary {A B : Type} {R : A → A → Prop} {abs : A → B} {rep : B → A}
  (Q : is_quotient R abs rep) {C : Type} {f : A → A → C}
  (H : forall (a a' b b' : A) (Ha : R a a') (Hb : R b b'), f a b = f a' b')
  {a b : A} (Ha : R a a) (Hb : R b b) : rec_binary Q f (abs a) (abs b) = f a b :=
have H2 : R a (rep (abs a)), from R_rep_abs Q Ha,
have H3 : R b (rep (abs b)), from R_rep_abs Q Hb,
calc
  rec_binary Q f (abs a) (abs b) = f (rep (abs a))  (rep (abs b)) : rfl
    ... = f a b : {(H _ _ _ _ H2 H3)⁻¹}

theorem comp_binary_refl {A B : Type} {R : A → A → Prop} {abs : A → B} {rep : B → A}
  (Q : is_quotient R abs rep) (Hrefl : reflexive R) {C : Type} {f : A → A → C}
  (H : forall (a a' b b' : A) (Ha : R a a') (Hb : R b b'), f a b = f a' b')
  (a b : A) : rec_binary Q f (abs a) (abs b) = f a b :=
comp_binary Q H (Hrefl a) (Hrefl b)

definition quotient_map {A B : Type} {R : A → A → Prop} {abs : A → B} {rep : B → A}
  (Q : is_quotient R abs rep) (f : A → A) (b : B) : B :=
abs (f (rep b))

theorem comp_quotient_map {A B : Type} {R : A → A → Prop} {abs : A → B} {rep : B → A}
  (Q : is_quotient R abs rep) {f : A → A}
  (H : forall (a a' : A) (Ha : R a a'), R (f a) (f a'))
  {a : A} (Ha : R a a) : quotient_map Q f (abs a) = abs (f a) :=
have H2 : R a (rep (abs a)), from R_rep_abs Q Ha,
have H3 : R (f a) (f (rep (abs a))), from H _ _ H2,
have H4 : abs (f a) = abs (f (rep (abs a))), from eq_abs Q H3,
H4⁻¹

definition quotient_map_binary {A B : Type} {R : A → A → Prop} {abs : A → B} {rep : B → A}
  (Q : is_quotient R abs rep) (f : A → A → A) (b c : B) : B :=
abs (f (rep b) (rep c))

theorem comp_quotient_map_binary {A B : Type} {R : A → A → Prop} {abs : A → B} {rep : B → A}
  (Q : is_quotient R abs rep) {f : A → A → A}
  (H : forall (a a' b b' : A) (Ha : R a a') (Hb : R b b'), R (f a b) (f a' b'))
  {a b : A} (Ha : R a a) (Hb : R b b) : quotient_map_binary Q f (abs a) (abs b) = abs (f a b) :=
have Ha2 : R a (rep (abs a)), from R_rep_abs Q Ha,
have Hb2 : R b (rep (abs b)), from R_rep_abs Q Hb,
have H2 : R (f a b) (f (rep (abs a)) (rep (abs b))), from H _ _ _ _ Ha2 Hb2,
(eq_abs Q H2)⁻¹

theorem comp_quotient_map_binary_refl {A B : Type} {R : A → A → Prop} (Hrefl : reflexive R)
  {abs : A → B} {rep : B → A} (Q : is_quotient R abs rep) {f : A → A → A}
  (H : forall (a a' b b' : A) (Ha : R a a') (Hb : R b b'), R (f a b) (f a' b'))
  (a b : A) : quotient_map_binary Q f (abs a) (abs b) = abs (f a b) :=
comp_quotient_map_binary Q H (Hrefl a) (Hrefl b)

/- image -/

definition image {A B : Type} (f : A → B) := subtype (fun b, ∃a, f a = b)

theorem image_inhabited {A B : Type} (f : A → B) (H : inhabited A) : inhabited (image f) :=
inhabited.mk (tag (f (default A)) (exists.intro (default A) rfl))

theorem image_inhabited2 {A B : Type} (f : A → B) (a : A) : inhabited (image f) :=
image_inhabited f (inhabited.mk a)

definition fun_image {A B : Type} (f : A → B) (a : A) : image f :=
tag (f a) (exists.intro a rfl)

theorem fun_image_def {A B : Type} (f : A → B) (a : A) :
  fun_image f a = tag (f a) (exists.intro a rfl) := rfl

theorem elt_of_fun_image {A B : Type} (f : A → B) (a : A) : elt_of (fun_image f a) = f a :=
by esimp

theorem image_elt_of {A B : Type} {f : A → B} (u : image f) : ∃a, f a = elt_of u :=
has_property u

theorem fun_image_surj {A B : Type} {f : A → B} (u : image f) : ∃a, fun_image f a = u :=
subtype.destruct u
  (take (b : B) (H : ∃a, f a = b),
    obtain a (H': f a = b), from H,
    (exists.intro a (tag_eq H')))

theorem image_tag {A B : Type} {f : A → B} (u : image f) : ∃a H, tag (f a) H = u :=
obtain a (H : fun_image f a = u), from fun_image_surj u,
exists.intro a (exists.intro (exists.intro a rfl) H)

open eq.ops

theorem fun_image_eq {A B : Type} (f : A → B) (a a' : A)
  : (f a = f a') ↔ (fun_image f a = fun_image f a') :=
iff.intro
  (assume H : f a = f a', tag_eq H)
  (assume H : fun_image f a = fun_image f a',
    by injection H; assumption)

theorem idempotent_image_elt_of {A : Type} {f : A → A} (H : ∀a, f (f a) = f a) (u : image f)
  : fun_image f (elt_of u) = u :=
obtain (a : A) (Ha : fun_image f a = u), from fun_image_surj u,
calc
  fun_image f (elt_of u) = fun_image f (elt_of (fun_image f a)) : by rewrite Ha
    ... = fun_image f (f a) : {elt_of_fun_image f a}
    ... = fun_image f a : {iff.elim_left (fun_image_eq f (f a) a) (H a)}
    ... = u : Ha

theorem idempotent_image_fix {A : Type} {f : A → A} (H : ∀a, f (f a) = f a) (u : image f)
  : f (elt_of u) = elt_of u :=
obtain (a : A) (Ha : f a = elt_of u), from image_elt_of u,
calc
  f (elt_of u) = f (f a) : {Ha⁻¹}
    ... = f a : H a
    ... = elt_of u : Ha

/- construct quotient from representative map -/

theorem representative_map_idempotent {A : Type} {R : A → A → Prop} {f : A → A}
    (H1 : ∀a, R a (f a)) (H2 : ∀a b, R a b ↔ R a a ∧ R b b ∧ f a = f b) (a : A) :
  f (f a) = f a :=
(and.elim_right (and.elim_right (iff.elim_left (H2 a (f a)) (H1 a))))⁻¹

theorem representative_map_idempotent_equiv {A : Type} {R : A → A → Prop} {f : A → A}
    (H1 : ∀a, R a (f a)) (H2 : ∀a b, R a b → f a = f b) (a : A) :
  f (f a) = f a :=
(H2 a (f a) (H1 a))⁻¹

theorem representative_map_refl_rep {A : Type} {R : A → A → Prop} {f : A → A}
    (H1 : ∀a, R a (f a)) (H2 : ∀a b, R a b ↔ R a a ∧ R b b ∧ f a = f b) (a : A) :
  R (f a) (f a) :=
representative_map_idempotent H1 H2 a ▸ H1 (f a)

theorem representative_map_image_fix {A : Type} {R : A → A → Prop} {f : A → A}
    (H1 : ∀a, R a (f a)) (H2 : ∀a a', R a a' ↔ R a a ∧ R a' a' ∧ f a = f a') (b : image f) :
  f (elt_of b) = elt_of b :=
idempotent_image_fix (representative_map_idempotent H1 H2) b

theorem representative_map_to_quotient {A : Type} {R : A → A → Prop} {f : A → A}
    (H1 : ∀a, R a (f a)) (H2 : ∀a a', R a a' ↔ R a a ∧ R a' a' ∧ f a = f a') :
  is_quotient R (fun_image f) elt_of :=
let abs := fun_image f in
intro
  (take u : image f,
    obtain (a : A) (Ha : f a = elt_of u), from image_elt_of u,
    have H : elt_of (abs (elt_of u)) = elt_of u, from
      calc
        elt_of (abs (elt_of u)) = f (elt_of u) : elt_of_fun_image _ _
          ... = f (f a) : {Ha⁻¹}
          ... = f a : representative_map_idempotent H1 H2 a
          ... = elt_of u : Ha,
    show abs (elt_of u) = u, from subtype.eq H)
  (take u : image f,
    show R (elt_of u) (elt_of u), from
      obtain (a : A) (Ha : f a = elt_of u), from image_elt_of u,
        Ha ▸ (@representative_map_refl_rep A R f H1 H2 a))
  (take a a',
    subst (fun_image_eq f a a') (H2 a a'))

theorem representative_map_equiv_inj {A : Type} {R : A → A → Prop}
    (equiv : is_equivalence R) {f : A → A}
    (H1 : ∀a, R a (f a)) (H2 : ∀a b, R a b → f a = f b) {a b : A} (H3 : f a = f b) :
  R a b :=
have symmR : relation.symmetric R, from rel_symm R,
have transR : relation.transitive R, from rel_trans R,
show R a b, from
  have H2 : R a (f b), from H3 ▸ (H1 a),
  have H3 : R (f b) b, from symmR (H1 b),
  transR H2 H3

theorem representative_map_to_quotient_equiv {A : Type} {R : A → A → Prop}
    (equiv : is_equivalence R) {f : A → A} (H1 : ∀a, R a (f a)) (H2 : ∀a b, R a b → f a = f b) :
  @is_quotient A (image f) R (fun_image f) elt_of :=
representative_map_to_quotient
  H1
  (take a b,
    have reflR : reflexive R, from rel_refl R,
    have H3 : f a = f b → R a b, from representative_map_equiv_inj equiv H1 H2,
    have H4 : R a b ↔ f a = f b, from iff.intro (H2 a b) H3,
    have H5 : R a b ↔ R b b ∧ f a = f b,
      from subst (symm (and_absorb_left _ (reflR b))) H4,
    subst (symm (and_absorb_left _ (reflR a))) H5)

end quotient
