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
list_induction_on s (refl _)
  (take x l,
    assume H : concat (concat l t) u = concat l (concat t u),
      calc concat (concat (cons x l) t) u = cons x (concat (concat l t) u) : refl _
                                      ... = concat (cons x l) (concat t u) : { H })

theorem concat_assoc3 (s t u : list T) : s ++ t ++ u = s ++ (t ++ u) :=
list_induction_on s (refl _)
  (take x l,
    assume H : concat (concat l t) u = concat l (concat t u),
      calc  concat (concat (cons x l) t) u = cons x (concat l (concat t u)) : { H }
                                       ... = concat (cons x l) (concat t u) : refl _)

theorem concat_assoc4 (s t u : list T) : s ++ t ++ u = s ++ (t ++ u) :=
list_induction_on s (refl _)
  (take x l,
    assume H : concat (concat l t) u = concat l (concat t u),
      calc
      concat (concat (cons x l) t) u = cons x (concat (concat l t) u) : refl _
        ... = cons x (concat l (concat t u)) : { H }
        ... = concat (cons x l) (concat t u) : refl _)

-- Length
-- ------

definition length : list T → ℕ := list.rec 0 (fun x l m, succ m)

-- TODO: cannot replace zero by 0
theorem length_nil : length (@nil T) = zero := refl _

theorem length_cons (x : T) (t : list T) : length (x :: t) = succ (length t) := refl _

theorem length_concat (s t : list T) : length (s ++ t) = length s + length t :=
list_induction_on s
  (calc
    length (concat nil t) = length t : refl _
      ... = 0 + length t : {symm !zero_add}
      ... = length (@nil T) + length t : refl _)
  (take x s,
    assume H : length (concat s t) = length s + length t,
    calc
      length (concat (cons x s) t ) = succ (length (concat s t))  : refl _
        ... = succ (length s + length t)  : { H }
        ... = succ (length s) + length t  : {symm !succ_add}
        ... = length (cons x s) + length t : refl _)

-- Reverse
-- -------

definition reverse : list T → list T := list.rec nil (fun x l r, r ++ [x])

theorem reverse_nil : reverse (@nil T) = nil := refl _

theorem reverse_cons (x : T) (l : list T) : reverse (x :: l) = (reverse l) ++ (cons x nil) := refl _

-- opaque_hint (hiding reverse)

theorem reverse_concat (s t : list T) : reverse (s ++ t) = (reverse t) ++ (reverse s) :=
list_induction_on s
  (calc
    reverse (concat nil t) = reverse t : { nil_concat _ }
      ... = concat (reverse t) nil : symm (concat_nil _)
      ... = concat (reverse t) (reverse nil) : {symm (reverse_nil)})
  (take x l,
    assume H : reverse (concat l t) = concat (reverse t) (reverse l),
    calc
      reverse (concat (cons x l) t) = concat (reverse (concat l t)) (cons x nil) : refl _
        ... = concat (concat (reverse t) (reverse l)) (cons x nil) : { H }
        ... = concat (reverse t) (concat (reverse l) (cons x nil)) : concat_assoc _ _ _
        ... = concat (reverse t) (reverse (cons x l)) : refl _)


-- -- add_rewrite length_nil length_cons
theorem reverse_reverse (l : list T) : reverse (reverse l) = l :=
list_induction_on l (refl _)
  (take x l',
    assume H: reverse (reverse l') = l',
    show reverse (reverse (cons x l')) = cons x l', from
      calc
        reverse (reverse (cons x l')) =
            concat (reverse (cons x nil)) (reverse (reverse l')) : {reverse_concat _ _}
          ... = cons x l' : {H})
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
list_induction_on l
  (calc
    append x nil = [x] : (refl _)
      ... = concat nil [x] : {symm (nil_concat _)}
      ... = concat (reverse nil) [x] : {symm (reverse_nil)}
      ... = reverse [x] : {symm (reverse_cons _ _)}
      ... = reverse (x :: (reverse nil)) : {symm (reverse_nil)})
  (take y l',
    assume H : append x l' = reverse (x :: reverse l'),
    calc
      append x (y :: l') = (y :: l') ++ [ x ] : append_eq_concat _ _
        ... = concat (reverse (reverse (y :: l'))) [ x ] : {symm (reverse_reverse _)}
        ... = reverse (x :: (reverse (y :: l'))) : refl _)
end
end list
