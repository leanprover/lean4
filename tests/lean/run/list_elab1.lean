----------------------------------------------------------------------------------------------------
--- Copyright (c) 2014 Parikshit Khanna. All rights reserved.
--- Released under Apache 2.0 license as described in the file LICENSE.
--- Authors: Parikshit Khanna, Jeremy Avigad
----------------------------------------------------------------------------------------------------

-- Theory list
-- ===========
--
-- Basic properties of lists.

import nat
using nat eq_proofs

inductive list (T : Type) : Type :=
| nil {} : list T
| cons : T → list T → list T

theorem list_induction_on {T : Type} {P : list T → Prop} (l : list T) (Hnil : P nil)
    (Hind : forall x : T, forall l : list T, forall H : P l, P (cons x l)) : P l :=
list_rec Hnil Hind l

definition concat {T : Type} (s t : list T) : list T :=
list_rec t (fun x : T, fun l : list T, fun u : list T, cons x u) s

theorem concat_nil {T : Type} (t : list T) : concat t nil = t :=
list_induction_on t (refl (concat nil nil))
  (take (x : T) (l : list T) (H : concat l nil = l),
    H ▸ (refl (concat (cons x l) nil)))
