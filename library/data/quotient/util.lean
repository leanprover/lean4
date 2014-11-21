-- Copyright (c) 2014 Floris van Doorn. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Floris van Doorn

import logic ..prod algebra.relation
import tools.fake_simplifier

open prod eq.ops
open fake_simplifier

namespace quotient

-- auxliary facts about products
-- -----------------------------

-- add_rewrite flip_pr1 flip_pr2 flip_pair
-- add_rewrite map_pair_pr1 map_pair_pr2 map_pair_pair
-- add_rewrite map_pair2_pr1 map_pair2_pr2 map_pair2_pair

theorem map_pair2_comm {A B : Type} {f : A → A → B} (Hcomm : ∀a b : A, f a b = f b a)
  (v w : A × A) : map_pair2 f v w = map_pair2 f w v :=
have Hx : pr1 (map_pair2 f v w) = pr1 (map_pair2 f w v), from
  calc
    pr1 (map_pair2 f v w) = f (pr1 v) (pr1 w) : map_pair2_pr1 f v w
      ... = f (pr1 w) (pr1 v) : Hcomm _ _
      ... = pr1 (map_pair2 f w v) : (map_pair2_pr1 f w v)⁻¹,
have Hy : pr2 (map_pair2 f v w) = pr2 (map_pair2 f w v), from
  calc
    pr2 (map_pair2 f v w) = f (pr2 v) (pr2 w) : map_pair2_pr2 f v w
      ... = f (pr2 w) (pr2 v) : Hcomm _ _
      ... = pr2 (map_pair2 f w v) : (map_pair2_pr2 f w v)⁻¹,
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
      ... = f (pr1 u) (pr1 (map_pair2 f v w)) : {(map_pair2_pr1 f _ _)⁻¹}
      ... = pr1 (map_pair2 f u (map_pair2 f v w)) : (map_pair2_pr1 f _ _)⁻¹,
have Hy : pr2 (map_pair2 f (map_pair2 f u v) w) =
          pr2 (map_pair2 f u (map_pair2 f v w)), from
  calc
     pr2 (map_pair2 f (map_pair2 f u v) w)
          = f (pr2 (map_pair2 f u v)) (pr2 w) : map_pair2_pr2 f _ _
      ... = f (f (pr2 u) (pr2 v)) (pr2 w) : {map_pair2_pr2 f _ _}
      ... = f (pr2 u) (f (pr2 v) (pr2 w)) : Hassoc (pr2 u) (pr2 v) (pr2 w)
      ... = f (pr2 u) (pr2 (map_pair2 f v w)) : {map_pair2_pr2 f _ _}
      ... = pr2 (map_pair2 f u (map_pair2 f v w)) : (map_pair2_pr2 f _ _)⁻¹,
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
prod.equal Hx Hy

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
prod.equal Hx Hy

end quotient
