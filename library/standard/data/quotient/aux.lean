-- Copyright (c) 2014 Floris van Doorn. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Floris van Doorn

import logic ..prod struc.relation
import tools.fake_simplifier

using prod eq_ops
using fake_simplifier

namespace quotient

-- auxliary facts about products
-- -----------------------------

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
have H2 : flip (flip a) = flip (flip b), from congr_arg flip H,
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

theorem map_pair_pr1 {A B : Type} (f : A → B) (a : A × A) : pr1 (map_pair f a) = f (pr1 a) :=
pr1_pair _ _

theorem map_pair_pr2 {A B : Type} (f : A → B) (a : A × A) : pr2 (map_pair f a) = f (pr2 a) :=
pr2_pair _ _

-- ### coordinatewise binary maps

definition map_pair2 {A B C : Type} (f : A → B → C) (a : A × A) (b : B × B) : C × C :=
pair (f (pr1 a) (pr1 b)) (f (pr2 a) (pr2 b))

theorem map_pair2_def {A B C : Type} (f : A → B → C) (a : A × A) (b : B × B) :
  map_pair2 f a b = pair (f (pr1 a) (pr1 b)) (f (pr2 a) (pr2 b)) := rfl

theorem map_pair2_pair {A B C : Type} (f : A → B → C) (a a' : A) (b b' : B) :
  map_pair2 f (pair a a') (pair b b') = pair (f a b) (f a' b') :=
calc
  map_pair2 f (pair a a') (pair b b')
        = pair (f (pr1 (pair a a')) b) (f (pr2 (pair a a')) (pr2 (pair b b')))
            : {pr1_pair b b'}
    ... = pair (f (pr1 (pair a a')) b) (f (pr2 (pair a a')) b') : {pr2_pair b b'}
    ... = pair (f (pr1 (pair a a')) b) (f a' b') : {pr2_pair a a'}
    ... = pair (f a b) (f a' b') : {pr1_pair a a'}

theorem map_pair2_pr1 {A B C : Type} (f : A → B → C) (a : A × A) (b : B × B) :
pr1 (map_pair2 f a b) = f (pr1 a) (pr1 b) := pr1_pair _ _

theorem map_pair2_pr2 {A B C : Type} (f : A → B → C) (a : A × A) (b : B × B) :
pr2 (map_pair2 f a b) = f (pr2 a) (pr2 b) := pr2_pair _ _

theorem map_pair2_flip {A B C : Type} (f : A → B → C) (a : A × A) (b : B × B) :
  flip (map_pair2 f a b) = map_pair2 f (flip a) (flip b) :=
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

end quotient
