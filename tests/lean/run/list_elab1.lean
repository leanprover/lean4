----------------------------------------------------------------------------------------------------
--- Copyright (c) 2014 Parikshit Khanna. All rights reserved.
--- Released under Apache 2.0 license as described in the file LICENSE.
--- Authors: Parikshit Khanna, Jeremy Avigad
----------------------------------------------------------------------------------------------------

-- Theory List
-- ===========
--
-- Basic properties of Lists.

open nat
inductive List (T : Type) : Type
| nil {} : List
| cons : T → List → List

namespace List
theorem List_induction_on {T : Type} {P : List T → Prop} (l : List T) (Hnil : P nil)
    (Hind : forall x : T, forall l : List T, forall H : P l, P (cons x l)) : P l :=
List.rec Hnil Hind l

definition concat {T : Type} (s t : List T) : List T :=
List.rec t (fun x : T, fun l : List T, fun u : List T, cons x u) s

attribute concat [reducible]
theorem concat_nil {T : Type} (t : List T) : concat t nil = t :=
List_induction_on t (eq.refl (concat nil nil))
  (take (x : T) (l : List T) (H : concat l nil = l),
    H ▸ (eq.refl (concat (cons x l) nil)))
end List
