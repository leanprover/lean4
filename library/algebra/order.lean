/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

This ports just the min function and theorems from the lean2 library; additional
functions will be ported in the future.
-/


/- min -/

definition min {A : Type} [has_le A] (a b : A) [decidable (a ≤ b)] : A :=
  if a ≤ b then a else b

theorem min_eq_left {A : Type} [has_le A] {a b : A} [decidable (a ≤ b)]
  (H : a ≤ b) : min a b = a := if_pos H

theorem min_eq_right {A : Type} [weak_order A] {x y : A}
           [p : decidable (x ≤ y)] (H : (y ≤ x)) : min x y = y :=
  let q : decidable (x ≤ y) := p in
  match q with
  | is_true h :=
      calc min x y = x : if_pos h
               ... = y : le_antisymm h H
  | is_false h := if_neg h
  end

theorem min_self {A : Type} [has_le A] (x : A) [p : decidable (x ≤ x)] : min x x = x :=
   let q : decidable (x ≤ x) := p in
   match q with
   | is_true  h := if_pos h
   | is_false h := if_neg h
   end
