-- Copyright (c) 2014 Floris van Doorn. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Floris van Doorn

import logic tools.tactic .subtype logic.connectives.cast struc.relation data.prod
import logic.connectives.instances

-- for now: to use substitution (iff_to_eq)
import logic.axioms.classical

-- for the last section
import logic.axioms.hilbert logic.axioms.funext

using relation prod tactic eq_proofs


-- temporary: substiution for iff
theorem substi {a b : Prop} {P : Prop → Prop} (H1 : a ↔ b) (H2 : P a) : P b :=
subst (iff_to_eq H1) H2

theorem transi {a b c : Prop} (H1 : a ↔ b) (H2 : b ↔ c) : a ↔ c :=
eq_to_iff (trans (iff_to_eq H1) (iff_to_eq H2))

theorem symmi {a b : Prop} (H : a ↔ b) : b ↔ a :=
eq_to_iff (symm (iff_to_eq H))

-- until we have the simplifier...
definition simp : tactic := apply @sorry


-- TODO: find a better name, and move to logic.connectives.basic
theorem and_inhabited_left {a : Prop} (b : Prop) (Ha : a) : a ∧ b ↔ b :=
iff_intro (take Hab, and_elim_right Hab) (take Hb, and_intro Ha Hb)


-- auxliary facts about products
-- -----------------------------

-- TODO: move to data.prod?

-- ### flip

definition flip {A B : Type} (a : A × B) : B × A := pair (pr2 a) (pr1 a)

theorem flip_def {A B : Type} (a : A × B) : flip a = pair (pr2 a) (pr1 a) := refl (flip a)

theorem flip_pair {A B : Type} (a : A) (b : B) : flip (pair a b) = pair b a := rfl

theorem flip_pr1 {A B : Type} (a : A × B) : pr1 (flip a) = pr2 a := rfl

theorem flip_pr2 {A B : Type} (a : A × B) : pr2 (flip a) = pr1 a := rfl

theorem flip_flip {A B : Type} (a : A × B) : flip (flip a) = a := 
pair_destruct a (take x y, rfl)

theorem P_flip {A B : Type} {P : A → B → Prop} {a : A × B} (H : P (pr1 a) (pr2 a))
  : P (pr2 (flip a)) (pr1 (flip a)) :=
(symm (flip_pr1 a)) ▸ (symm (flip_pr2 a)) ▸ H

theorem flip_inj {A B : Type} {a b : A × B} (H : flip a = flip b) : a = b :=
have H2 : flip (flip a) = flip (flip b), from congr2 flip H,
show a = b, from (flip_flip a) ▸ (flip_flip b) ▸ H2

-- ### coordinatewise unary maps

definition map_pair {A B : Type} (f : A → B) (a : A × A) : B × B := 
pair (f (pr1 a)) (f (pr2 a))

theorem map_pair_def {A B : Type} (f : A → B) (a : A × A)
  : map_pair f a = pair (f (pr1 a)) (f (pr2 a)) := 
rfl

theorem map_pair_pair {A B : Type} (f : A → B) (a a' : A)
  : map_pair f (pair a a') = pair (f a) (f a') := 
(pr1_pair a a') ▸ (pr2_pair a a') ▸ (rfl)

theorem map_pair_pr1 {A B : Type} (f : A → B) (a : A × A) : pr1 (map_pair f a) = f (pr1 a)
:= pr1_pair _ _

theorem map_pair_pr2 {A B : Type} (f : A → B) (a : A × A) : pr2 (map_pair f a) = f (pr2 a)
:= pr2_pair _ _

-- ### coordinatewise binary maps

definition map_pair2 {A B C : Type} (f : A → B → C) (a : A × A) (b : B × B) : C × C
:= pair (f (pr1 a) (pr1 b)) (f (pr2 a) (pr2 b))

theorem map_pair2_def {A B C : Type} (f : A → B → C) (a : A × A) (b : B × B)
  : map_pair2 f a b = pair (f (pr1 a) (pr1 b)) (f (pr2 a) (pr2 b)) := rfl

theorem map_pair2_pair {A B C : Type} (f : A → B → C) (a a' : A) (b b' : B)
  : map_pair2 f (pair a a') (pair b b') = pair (f a b) (f a' b') :=
calc
  map_pair2 f (pair a a') (pair b b')
	= pair (f (pr1 (pair a a')) b) (f (pr2 (pair a a')) (pr2 (pair b b')))
	    : {pr1_pair b b'}
    ... = pair (f (pr1 (pair a a')) b) (f (pr2 (pair a a')) b') : {pr2_pair b b'}
    ... = pair (f (pr1 (pair a a')) b) (f a' b') : {pr2_pair a a'}
    ... = pair (f a b) (f a' b') : {pr1_pair a a'}

theorem map_pair2_pr1 {A B C : Type} (f : A → B → C) (a : A × A) (b : B × B)
  : pr1 (map_pair2 f a b) = f (pr1 a) (pr1 b) := pr1_pair _ _

theorem map_pair2_pr2 {A B C : Type} (f : A → B → C) (a : A × A) (b : B × B)
  : pr2 (map_pair2 f a b) = f (pr2 a) (pr2 b) := pr2_pair _ _

theorem map_pair2_flip {A B C : Type} (f : A → B → C) (a : A × A) (b : B × B)
  : flip (map_pair2 f a b) = map_pair2 f (flip a) (flip b) :=
  have Hx : pr1 (flip (map_pair2 f a b)) =  pr1 (map_pair2 f (flip a) (flip b)), from
    calc
      pr1 (flip (map_pair2 f a b)) = pr2 (map_pair2 f a b) : flip_pr1 _
        ... = f (pr2 a) (pr2 b) : map_pair2_pr2 f a b
        ... = f (pr1 (flip a)) (pr2 b) : {symm (flip_pr1 a)}
        ... = f (pr1 (flip a)) (pr1 (flip b)) : {symm (flip_pr1 b)}
        ... = pr1 (map_pair2 f (flip a) (flip b)) : symm (map_pair2_pr1 f _ _),
  have Hy : pr2 (flip (map_pair2 f a b)) =  pr2 (map_pair2 f (flip a) (flip b)), from
    calc
      pr2 (flip (map_pair2 f a b)) = pr1 (map_pair2 f a b) : flip_pr2 _
        ... = f (pr1 a) (pr1 b) : map_pair2_pr1 f a b
        ... = f (pr2 (flip a)) (pr1 b) : {symm (flip_pr2 a)}
        ... = f (pr2 (flip a)) (pr2 (flip b)) : {symm (flip_pr2 b)}
        ... = pr2 (map_pair2 f (flip a) (flip b)) : symm (map_pair2_pr2 f _ _),
  pair_eq Hx Hy

-- add_rewrite flip_pr1 flip_pr2 flip_pair
-- add_rewrite map_pair_pr1 map_pair_pr2 map_pair_pair
-- add_rewrite map_pair2_pr1 map_pair2_pr2 map_pair2_pair

theorem map_pair2_comm {A B : Type} {f : A → A → B} (Hcomm : ∀a b : A, f a b = f b a)
  (v w : A × A) : map_pair2 f v w = map_pair2 f w v :=
have Hx : pr1 (map_pair2 f v w) = pr1 (map_pair2 f w v), from
  calc
    pr1 (map_pair2 f v w) = f (pr1 v) (pr1 w) : map_pair2_pr1 f v w
      ... = f (pr1 w) (pr1 v) : Hcomm _ _
      ... = pr1 (map_pair2 f w v) : symm (map_pair2_pr1 f w v),
have Hy : pr2 (map_pair2 f v w) = pr2 (map_pair2 f w v), from
  calc
    pr2 (map_pair2 f v w) = f (pr2 v) (pr2 w) : map_pair2_pr2 f v w
      ... = f (pr2 w) (pr2 v) : Hcomm _ _
      ... = pr2 (map_pair2 f w v) : symm (map_pair2_pr2 f w v),
pair_eq Hx Hy

theorem map_pair2_assoc {A : Type} {f : A → A → A}
    (Hassoc : ∀a b c : A, f (f a b) c = f a (f b c)) (u v w : A × A) : 
  map_pair2 f (map_pair2 f u v) w = map_pair2 f u (map_pair2 f v w) :=
have Hx : pr1 (map_pair2 f (map_pair2 f u v) w) =
	  pr1 (map_pair2 f u (map_pair2 f v w)), from
  calc
     pr1 (map_pair2 f (map_pair2 f u v) w)
	  = f (pr1 (map_pair2 f u v)) (pr1 w) : map_pair2_pr1 f _ _
      ... = f (f (pr1 u) (pr1 v)) (pr1 w) : {map_pair2_pr1 f _ _}
      ... = f (pr1 u) (f (pr1 v) (pr1 w)) : Hassoc (pr1 u) (pr1 v) (pr1 w)
      ... = f (pr1 u) (pr1 (map_pair2 f v w)) : {symm (map_pair2_pr1 f _ _)}
      ... = pr1 (map_pair2 f u (map_pair2 f v w)) : symm (map_pair2_pr1 f _ _),
have Hy : pr2 (map_pair2 f (map_pair2 f u v) w) =
	  pr2 (map_pair2 f u (map_pair2 f v w)), from
  calc
     pr2 (map_pair2 f (map_pair2 f u v) w)
	  = f (pr2 (map_pair2 f u v)) (pr2 w) : map_pair2_pr2 f _ _
      ... = f (f (pr2 u) (pr2 v)) (pr2 w) : {map_pair2_pr2 f _ _}
      ... = f (pr2 u) (f (pr2 v) (pr2 w)) : Hassoc (pr2 u) (pr2 v) (pr2 w)
      ... = f (pr2 u) (pr2 (map_pair2 f v w)) : {symm (map_pair2_pr2 f _ _)}
      ... = pr2 (map_pair2 f u (map_pair2 f v w)) : symm (map_pair2_pr2 f _ _),
pair_eq Hx Hy

theorem map_pair2_id_right {A B : Type} {f : A → B → A} {e : B} (Hid : ∀a : A, f a e = a) 
  (v : A × A) : map_pair2 f v (pair e e) = v :=
have Hx : pr1 (map_pair2 f v (pair e e)) = pr1 v, from
  (calc
    pr1 (map_pair2 f v (pair e e)) = f (pr1 v) (pr1 (pair e e)) : by simp
      ... = f (pr1 v) e : by simp
      ... = pr1 v : Hid (pr1 v)),
have Hy : pr2 (map_pair2 f v (pair e e)) = pr2 v, from
  (calc
    pr2 (map_pair2 f v (pair e e)) = f (pr2 v) (pr2 (pair e e)) : by simp
      ... = f (pr2 v) e : by simp
      ... = pr2 v : Hid (pr2 v)),
prod_eq Hx Hy

theorem map_pair2_id_left {A B : Type} {f : B → A → A} {e : B} (Hid : ∀a : A, f e a = a)
  (v : A × A) : map_pair2 f (pair e e) v = v :=
have Hx : pr1 (map_pair2 f (pair e e) v) = pr1 v, from
   calc
    pr1 (map_pair2 f (pair e e) v) = f (pr1 (pair e e)) (pr1 v) : by simp
      ... = f e (pr1 v) : by simp
      ... = pr1 v : Hid (pr1 v),
have Hy : pr2 (map_pair2 f (pair e e) v) = pr2 v, from
   calc
    pr2 (map_pair2 f (pair e e) v) = f (pr2 (pair e e)) (pr2 v) : by simp
      ... = f e (pr2 v) : by simp
      ... = pr2 v : Hid (pr2 v),
prod_eq Hx Hy

opaque_hint (hiding flip map_pair map_pair2)


-- Theory data.quotient
-- ====================

namespace quotient

using subtype

-- definition and basics
-- ---------------------

-- TODO: make this a structure
definition is_quotient {A B : Type} (R : A → A → Prop) (abs : A → B) (rep : B → A) : Prop :=
  (∀b, abs (rep b) = b) ∧
  (∀b, R (rep b) (rep b)) ∧
  (∀r s, R r s ↔ (R r r ∧ R s s ∧ abs r = abs s))

theorem intro {A B : Type} {R : A → A → Prop} {abs : A → B} {rep : B → A}
  (H1 : ∀b, abs (rep b) = b) (H2 : ∀b, R (rep b) (rep b))
  (H3 : ∀r s, R r s ↔ (R r r ∧ R s s ∧ abs r = abs s)) : is_quotient R abs rep := 
and_intro H1 (and_intro H2 H3)

-- theorem intro_refl {A B : Type} {R : A → A → Prop} {abs : A → B} {rep : B → A}
--   (H1 : reflexive R) (H2 : ∀b, abs (rep b) = b)
--   (H3 : ∀r s, R r s ↔ abs r = abs s) : is_quotient R abs rep :=
-- intro
--   H2
--   (take b, H1 (rep b))
--   (take r s,
--     have H4 : R r s ↔ R s s ∧ abs r = abs s,
--       from 
--         gensubst.subst (relation.operations.symm (and_inhabited_left _ (H1 s))) (H3 r s),
--     gensubst.subst (relation.operations.symm (and_inhabited_left _ (H1 r))) H4)

-- these work now, but the above still does not
-- theorem test (a b c : Prop) (P : Prop → Prop) (H1 : a ↔ b) (H2 : c ∧ a) : c ∧ b :=
-- gensubst.subst H1 H2

-- theorem test2 {A : Type} {R : A → A → Prop} (Q : Prop) (r s : A) 
--   (H3 : R r s ↔ Q) (H1 : R s s) : Q ↔ (R s s ∧ Q) :=
-- relation.operations.symm (and_inhabited_left Q H1)

-- theorem test3 {A : Type} {R : A → A → Prop} (Q : Prop) (r s : A) 
--   (H3 : R r s ↔ Q) (H1 : R s s) : R r s ↔ (R s s ∧ Q) :=
-- gensubst.subst (test2 Q r s H3 H1) H3

-- theorem test4 {A : Type} {R : A → A → Prop} (Q : Prop) (r s : A) 
--   (H3 : R r s ↔ Q) (H1 : R s s) : R r s ↔ (R s s ∧ Q) :=
-- gensubst.subst (relation.operations.symm (and_inhabited_left Q H1)) H3

theorem intro_refl {A B : Type} {R : A → A → Prop} {abs : A → B} {rep : B → A}
  (H1 : reflexive R) (H2 : ∀b, abs (rep b) = b)
  (H3 : ∀r s, R r s ↔ abs r = abs s) : is_quotient R abs rep :=
intro
  H2
  (take b, H1 (rep b))
  (take r s,
    have H4 : R r s ↔ R s s ∧ abs r = abs s,
      from 
        substi (symmi (and_inhabited_left _ (H1 s))) (H3 r s),
    substi (symmi (and_inhabited_left _ (H1 r))) H4)

theorem abs_rep {A B : Type} {R : A → A → Prop} {abs : A → B} {rep : B → A}
  (Q : is_quotient R abs rep) (b : B) :  abs (rep b) = b := 
and_elim_left Q b

theorem refl_rep {A B : Type} {R : A → A → Prop} {abs : A → B} {rep : B → A}
  (Q : is_quotient R abs rep) (b : B) : R (rep b) (rep b) := 
and_elim_left (and_elim_right Q) b

theorem R_iff {A B : Type} {R : A → A → Prop} {abs : A → B} {rep : B → A}
  (Q : is_quotient R abs rep) (r s : A) : R r s ↔ (R r r ∧ R s s ∧ abs r = abs s) :=
and_elim_right (and_elim_right Q) r s

theorem refl_left {A B : Type} {R : A → A → Prop} {abs : A → B} {rep : B → A}
  (Q : is_quotient R abs rep) {r s : A} (H : R r s) : R r r :=
and_elim_left (iff_elim_left (R_iff Q r s) H)

theorem refl_right {A B : Type} {R : A → A → Prop} {abs : A → B} {rep : B → A}
  (Q : is_quotient R abs rep) {r s : A} (H : R r s) : R s s :=
and_elim_left (and_elim_right (iff_elim_left (R_iff Q r s) H))

theorem eq_abs {A B : Type} {R : A → A → Prop} {abs : A → B} {rep : B → A}
  (Q : is_quotient R abs rep) {r s : A} (H : R r s) : abs r = abs s :=
and_elim_right (and_elim_right (iff_elim_left (R_iff Q r s) H))

theorem R_intro {A B : Type} {R : A → A → Prop} {abs : A → B} {rep : B → A}
  (Q : is_quotient R abs rep) {r s : A} (H1 : R r r) (H2 : R s s) (H3 : abs r = abs s) : R r s :=
iff_elim_right (R_iff Q r s) (and_intro H1 (and_intro H2 H3))

theorem R_intro_refl {A B : Type} {R : A → A → Prop} {abs : A → B} {rep : B → A}
  (Q : is_quotient R abs rep) (H1 : reflexive R) {r s : A} (H2 : abs r = abs s) : R r s :=
iff_elim_right (R_iff Q r s) (and_intro (H1 r) (and_intro (H1 s) H2))

theorem rep_eq {A B : Type} {R : A → A → Prop} {abs : A → B} {rep : B → A}
  (Q : is_quotient R abs rep) {a b : B} (H : R (rep a) (rep b)) : a = b :=
calc
  a = abs (rep a) : symm (abs_rep Q a)
    ... = abs (rep b) : {eq_abs Q H}
    ... = b : abs_rep Q b

theorem R_rep_abs {A B : Type} {R : A → A → Prop} {abs : A → B} {rep : B → A}
  (Q : is_quotient R abs rep) {a : A} (H : R a a) : R a (rep (abs a)) :=
have H3 : abs a = abs (rep (abs a)), from symm (abs_rep Q (abs a)),
R_intro Q H (refl_rep Q (abs a)) H3

theorem quotient_imp_symm {A B : Type} {R : A → A → Prop} {abs : A → B} {rep : B → A}
  (Q : is_quotient R abs rep) : symmetric R :=
take a b : A,
assume H : R a b,
have Ha : R a a, from refl_left Q H,
have Hb : R b b, from refl_right Q H,
have Hab : abs b = abs a, from symm (eq_abs Q H),
R_intro Q Hb Ha Hab

theorem quotient_imp_trans {A B : Type} {R : A → A → Prop} {abs : A → B} {rep : B → A}
  (Q : is_quotient R abs rep) : transitive R :=
take a b c : A,
assume Hab : R a b,
assume Hbc : R b c,
have Ha : R a a, from refl_left Q Hab,
have Hc : R c c, from refl_right Q Hbc,
have Hac : abs a = abs c, from trans (eq_abs Q Hab) (eq_abs Q Hbc),
R_intro Q Ha Hc Hac

-- recursion
-- ---------

-- (maybe some are superfluous)

definition rec {A B : Type} {R : A → A → Prop} {abs : A → B} {rep : B → A}
  (Q : is_quotient R abs rep) {C : B → Type} (f : forall (a : A), C (abs a)) (b : B) : C b :=
eq_rec_on (abs_rep Q b) (f (rep b))

theorem comp {A B : Type} {R : A → A → Prop} {abs : A → B} {rep : B → A}
  (Q : is_quotient R abs rep) {C : B → Type} {f : forall (a : A), C (abs a)}
  (H : forall (r s : A) (H' : R r s), eq_rec_on (eq_abs Q H') (f r) = f s)
  {a : A} (Ha : R a a) : rec Q f (abs a) = f a :=
have H2 [fact] : R a (rep (abs a)), from R_rep_abs Q Ha,
calc
  rec Q f (abs a) =  eq_rec_on _ (f (rep (abs a))) : rfl 
    ... = eq_rec_on _ (eq_rec_on _ (f a)) : {symm (H _ _ H2)}
    ... = eq_rec_on _ (f a) : eq_rec_on_compose _ _ _
    ... = f a : eq_rec_on_id _ _

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
    ... = f a : {symm (H _ _ H2)}

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
    ... = f a b : {symm (H _ _ _ _ H2 H3)}

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
symm H4

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
symm (eq_abs Q H2)

theorem comp_quotient_map_binary_refl {A B : Type} {R : A → A → Prop} (Hrefl : reflexive R)
  {abs : A → B} {rep : B → A} (Q : is_quotient R abs rep) {f : A → A → A}
  (H : forall (a a' b b' : A) (Ha : R a a') (Hb : R b b'), R (f a b) (f a' b'))
  (a b : A) : quotient_map_binary Q f (abs a) (abs b) = abs (f a b) :=
comp_quotient_map_binary Q H (Hrefl a) (Hrefl b)

opaque_hint (hiding rec rec_constant rec_binary quotient_map quotient_map_binary)


-- image
-- -----

-- has to be an abbreviation, so that fun_image_definition below will typecheck outside
-- the file
abbreviation image {A B : Type} (f : A → B) := subtype (fun b, ∃a, f a = b)

theorem image_inhabited {A B : Type} (f : A → B) (H : inhabited A) : inhabited (image f) :=
inhabited_intro (tag (f (default A)) (exists_intro (default A) rfl))

theorem image_inhabited2 {A B : Type} (f : A → B) (a : A) : inhabited (image f) :=
image_inhabited f (inhabited_intro a)

definition fun_image {A B : Type} (f : A → B) (a : A) : image f :=
tag (f a) (exists_intro a rfl)

theorem fun_image_def {A B : Type} (f : A → B) (a : A) : 
  fun_image f a = tag (f a) (exists_intro a rfl) := rfl

theorem elt_of_fun_image {A B : Type} (f : A → B) (a : A) : elt_of (fun_image f a) = f a :=
elt_of_tag _ _

theorem image_elt_of {A B : Type} {f : A → B} (u : image f) : ∃a, f a = elt_of u :=
has_property u

theorem fun_image_surj {A B : Type} {f : A → B} (u : image f) : ∃a, fun_image f a = u :=
subtype_destruct u 
  (take (b : B) (H : ∃a, f a = b),
    obtain a (H': f a = b), from H,
    (exists_intro a (tag_eq H')))

theorem image_tag {A B : Type} {f : A → B} (u : image f) : ∃a H, tag (f a) H = u :=
obtain a (H : fun_image f a = u), from fun_image_surj u,
exists_intro a (exists_intro (exists_intro a rfl) H)

theorem fun_image_eq {A B : Type} (f : A → B) (a a' : A)
  : (f a = f a') ↔ (fun_image f a = fun_image f a') :=
iff_intro
  (assume H : f a = f a', tag_eq H)
  (assume H : fun_image f a = fun_image f a',
    subst (subst (congr2 elt_of H) (elt_of_fun_image f a)) (elt_of_fun_image f a'))

theorem idempotent_image_elt_of {A : Type} {f : A → A} (H : ∀a, f (f a) = f a) (u : image f)
  : fun_image f (elt_of u) = u :=
obtain (a : A) (Ha : fun_image f a = u), from fun_image_surj u,
calc
  fun_image f (elt_of u) = fun_image f (elt_of (fun_image f a)) : {symm Ha}
    ... = fun_image f (f a) : {elt_of_fun_image f a}
    ... = fun_image f a : {iff_elim_left (fun_image_eq f (f a) a) (H a)}
    ... = u : Ha

theorem idempotent_image_fix {A : Type} {f : A → A} (H : ∀a, f (f a) = f a) (u : image f)
  : f (elt_of u) = elt_of u :=
obtain (a : A) (Ha : f a = elt_of u), from image_elt_of u,
calc
  f (elt_of u) = f (f a) : {symm Ha}
    ... = f a : H a
    ... = elt_of u : Ha


-- construct quotient from representative map
-- ------------------------------------------

theorem representative_map_idempotent {A : Type} {R : A → A → Prop} {f : A → A}
  (H1 : ∀a, R a (f a)) (H2 : ∀a b, R a b ↔ R a a ∧ R b b ∧ f a = f b) (a : A)
  : f (f a) = f a :=
symm (and_elim_right (and_elim_right (iff_elim_left (H2 a (f a)) (H1 a))))

theorem representative_map_idempotent_equiv {A : Type} {R : A → A → Prop} {f : A → A}
  (H1 : ∀a, R a (f a)) (H2 : ∀a b, R a b → f a = f b) (a : A)
  : f (f a) = f a :=
symm (H2 a (f a) (H1 a))

theorem representative_map_refl_rep {A : Type} {R : A → A → Prop} {f : A → A}
  (H1 : ∀a, R a (f a)) (H2 : ∀a b, R a b ↔ R a a ∧ R b b ∧ f a = f b) (a : A)
  : R (f a) (f a) :=
subst (representative_map_idempotent H1 H2 a) (H1 (f a)) 

theorem representative_map_image_fix {A : Type} {R : A → A → Prop} {f : A → A}
  (H1 : ∀a, R a (f a)) (H2 : ∀a a', R a a' ↔ R a a ∧ R a' a' ∧ f a = f a') (b : image f)
  : f (elt_of b) = elt_of b :=
idempotent_image_fix (representative_map_idempotent H1 H2) b

theorem representative_map_to_quotient {A : Type} {R : A → A → Prop} {f : A → A}
  (H1 : ∀a, R a (f a)) (H2 : ∀a a', R a a' ↔ R a a ∧ R a' a' ∧ f a = f a')
  : is_quotient _ (fun_image f) elt_of :=
let abs [inline] := fun_image f in
intro
  (take u : image f,
    obtain (a : A) (Ha : f a = elt_of u), from image_elt_of u,
    have H : elt_of (abs (elt_of u)) = elt_of u, from
      calc
        elt_of (abs (elt_of u)) = f (elt_of u) : elt_of_fun_image _ _
          ... = f (f a) : {symm Ha}
          ... = f a : representative_map_idempotent H1 H2 a
          ... = elt_of u : Ha,
    show abs (elt_of u) = u, from subtype_eq H)
  (take u : image f,
    show R (elt_of u) (elt_of u), from
      obtain (a : A) (Ha : f a = elt_of u), from image_elt_of u,
        subst Ha (@representative_map_refl_rep A R f H1 H2 a))
  (take a a', 
    substi (fun_image_eq f a a') (H2 a a'))

-- TODO: fix these
-- e.g. in the next three lemmas, we should not need to specify the equivalence relation
-- but the class inference finds reflexive.class eq
theorem equiv_is_refl {A : Type} {R : A → A → Prop} (equiv : is_equivalence.class R) :=
@operations.refl _ R (@is_equivalence.is_reflexive _ _ equiv)
-- we should be able to write
-- @operations.refl _ R _

theorem equiv_is_symm {A : Type} {R : A → A → Prop} (equiv : is_equivalence.class R) :=
@operations.symm _ R (@is_equivalence.is_symmetric _ _ equiv)

theorem equiv_is_trans {A : Type} {R : A → A → Prop} (equiv : is_equivalence.class R) :=
@operations.trans _ R (@is_equivalence.is_transitive _ _ equiv)

theorem representative_map_equiv_inj {A : Type} {R : A → A → Prop}
  (equiv : is_equivalence.class R) {f : A → A} (H1 : ∀a, R a (f a)) (H2 : ∀a b, R a b → f a = f b)
  {a b : A} (H3 : f a = f b) : R a b :=
-- have symmR : symmetric R, from @relation.operations.symm _ R _,
have symmR : symmetric R, from equiv_is_symm equiv,
have transR : transitive R, from equiv_is_trans equiv,
show R a b, from
  have H2 : R a (f b), from subst H3 (H1 a),
  have H3 : R (f b) b, from symmR _ _ (H1 b),
  transR _ _ _ H2 H3

theorem representative_map_to_quotient_equiv {A : Type} {R : A → A → Prop}
  (equiv : is_equivalence.class R) {f : A → A} (H1 : ∀a, R a (f a)) (H2 : ∀a b, R a b → f a = f b)
  : @is_quotient A (image f) R (fun_image f) elt_of :=
representative_map_to_quotient
  H1
  (take a b,
    have reflR : reflexive R, from equiv_is_refl equiv,
    have H3 : f a = f b → R a b, from representative_map_equiv_inj equiv H1 H2,
    have H4 : R a b ↔ f a = f b, from iff_intro (H2 a b) H3,
    have H5 : R a b ↔ R b b ∧ f a = f b,
      from substi (symmi (and_inhabited_left _ (reflR b))) H4,
    substi (symmi (and_inhabited_left _ (reflR a))) H5)

-- TODO: split this into another file -- it depends on hilbert

-- abstract quotient
-- -----------------

definition prelim_map {A : Type} (R : A → A → Prop) (a : A) :=
-- TODO: it is interesting how the elaborator fails here
-- epsilon (fun b, R a b)
@epsilon _ (nonempty_intro a) (fun b, R a b)

-- TODO: only needed R reflexive (or weaker: R a a)
theorem prelim_map_rel {A : Type} {R : A → A → Prop} (H : is_equivalence.class R) (a : A)
  : R a (prelim_map R a) :=
have reflR : reflexive R, from equiv_is_refl H,
epsilon_spec (exists_intro a (reflR a))

-- TODO: only needed: R PER
theorem prelim_map_congr {A : Type} {R : A → A → Prop} (H1 : is_equivalence.class R) {a b : A}
  (H2 : R a b) : prelim_map R a = prelim_map R b :=
have symmR : symmetric R, from equiv_is_symm H1,
have transR : transitive R, from equiv_is_trans H1,
have H3 : ∀c, R a c ↔ R b c, from
  take c,
    iff_intro
      (assume H4 : R a c, transR b a c (symmR a b H2) H4)
      (assume H4 : R b c, transR a b c H2 H4),
have H4 : (fun c, R a c) = (fun c, R b c), from funext (take c, iff_to_eq (H3 c)),
show @epsilon _ (nonempty_intro a) (λc, R a c) = @epsilon _ (nonempty_intro b) (λc, R b c), 
  from congr2 _ H4

definition quotient {A : Type} (R : A → A → Prop) : Type := image (prelim_map R)

definition quotient_abs {A : Type} (R : A → A → Prop) : A → quotient R :=
fun_image (prelim_map R)

definition quotient_elt_of {A : Type} (R : A → A → Prop) : quotient R → A := elt_of

theorem quotient_is_quotient  {A : Type} (R : A → A → Prop) (H : is_equivalence.class R)
  : is_quotient R (quotient_abs R) (quotient_elt_of R) :=
representative_map_to_quotient_equiv
  H
  (prelim_map_rel H)
  (@prelim_map_congr _ _ H)

-- previously:
-- opaque_hint (hiding fun_image rec is_quotient prelim_map)
-- transparent: image, image_incl, quotient, quotient_abs, quotient_rep

end quotient
