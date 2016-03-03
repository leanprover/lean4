----------------------------------------------------------------------------------------------------
--- Copyright (c) 2014 Parikshit Khanna. All rights reserved.
--- Released under Apache 2.0 license as described in the file LICENSE.
--- Authors: Parikshit Khanna, Jeremy Avigad
----------------------------------------------------------------------------------------------------

-- Theory list
-- ===========
--
-- Basic properties of lists.

import logic data.nat
-- import congr

open nat algebra
-- open congr
open eq.ops eq

inductive list (T : Type) : Type :=
| nil {} : list T
| cons : T → list T → list T

definition refl := @eq.refl

namespace list

-- Type
-- ----

infixr `::` := cons

section

variable {T : Type}

theorem list_induction_on {P : list T → Prop} (l : list T) (Hnil : P nil)
    (Hind : forall x : T, forall l : list T, forall H : P l, P (cons x l)) : P l :=
list.rec Hnil Hind l

theorem list_cases_on {P : list T → Prop} (l : list T) (Hnil : P nil)
    (Hcons : forall x : T, forall l : list T, P (cons x l)) : P l :=
list_induction_on l Hnil (take x l IH, Hcons x l)

notation `[` l:(foldr `,` (h t, cons h t) nil) `]` := l


-- Concat
-- ------

definition concat (s t : list T) : list T :=
list.rec t (fun x : T, fun l : list T, fun u : list T, cons x u) s

infixl `++` := concat

theorem nil_concat (t : list T) : nil ++ t = t := refl _

theorem cons_concat (x : T) (s t : list T) : (x :: s) ++ t = x :: (s ++ t) := refl _

theorem concat_nil (t : list T) : t ++ nil = t :=
list_induction_on t (refl _)
  (take (x : T) (l : list T) (H : concat l nil = l),
    H ▸ (refl (cons x (concat l nil))))

attribute concat [reducible]
theorem concat_nil2 (t : list T) : t ++ nil = t :=
list_induction_on t (refl _)
  (take (x : T) (l : list T) (H : concat l nil = l),
    -- H ▸ (refl (cons x (concat l nil))))
    H ▸ (refl (concat (cons x l) nil)))

theorem concat_assoc (s t u : list T) : s ++ t ++ u = s ++ (t ++ u) :=
list_induction_on s (refl _)
  (take x l,
    assume H : concat (concat l t) u = concat l (concat t u),
    H ▸ refl _)

theorem concat_assoc2 (s t u : list T) : s ++ t ++ u = s ++ (t ++ u) :=
sorry


theorem concat_assoc3 (s t u : list T) : s ++ t ++ u = s ++ (t ++ u) :=
sorry

theorem concat_assoc4 (s t u : list T) : s ++ t ++ u = s ++ (t ++ u) :=
sorry

-- Length
-- ------

definition length : list T → ℕ := list.rec 0 (fun x l m, succ m)

-- TODO: cannot replace zero by 0
theorem length_nil : length (@nil T) = zero := refl _

theorem length_cons (x : T) (t : list T) : length (x :: t) = succ (length t) := refl _

theorem length_concat (s t : list T) : length (s ++ t) = length s + length t :=
sorry

-- Reverse
-- -------

definition reverse : list T → list T := list.rec nil (fun x l r, r ++ [x])

theorem reverse_nil : reverse (@nil T) = nil := refl _

theorem reverse_cons (x : T) (l : list T) : reverse (x :: l) = (reverse l) ++ (cons x nil) := refl _

-- opaque_hint (hiding reverse)

theorem reverse_concat (s t : list T) : reverse (s ++ t) = (reverse t) ++ (reverse s) :=
sorry

-- -- add_rewrite length_nil length_cons
theorem reverse_reverse (l : list T) : reverse (reverse l) = l :=
sorry
-- Append
-- ------

-- TODO: define reverse from append

definition append (x : T) : list T → list T := list.rec (x :: nil) (fun y l l', y :: l')

theorem append_nil (x : T) : append x nil = [x] := refl _

theorem append_cons (x : T) (y : T) (l : list T) : append x (y :: l)  = y :: (append x l) := refl _

theorem append_eq_concat  (x : T) (l : list T) : append x l = l ++ [x] :=
list_induction_on l (refl _)
  (take y l,
    assume P : append x l = concat l [x],
    P ▸ refl _)

theorem append_eq_reverse_cons  (x : T) (l : list T) : append x l = reverse (x :: reverse l) :=
sorry

end
end list
