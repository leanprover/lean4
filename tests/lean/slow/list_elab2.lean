----------------------------------------------------------------------------------------------------
--- Copyright (c) 2014 Parikshit Khanna. All rights reserved.
--- Released under Apache 2.0 license as described in the file LICENSE.
--- Authors: Parikshit Khanna, Jeremy Avigad
----------------------------------------------------------------------------------------------------

-- Theory list
-- ===========
--
-- Basic properties of lists.

import tactic
import nat
-- import congr

set_option unifier.expensive true
using nat
-- using congr
using eq_proofs

namespace list


-- Type
-- ----

inductive list (T : Type) : Type :=
| nil {} : list T
| cons : T → list T → list T

infix `::` : 65 := cons

section

variable {T : Type}

theorem list_induction_on {P : list T → Prop} (l : list T) (Hnil : P nil)
    (Hind : forall x : T, forall l : list T, forall H : P l, P (cons x l)) : P l :=
list_rec Hnil Hind l

theorem list_cases_on {P : list T → Prop} (l : list T) (Hnil : P nil)
    (Hcons : forall x : T, forall l : list T, P (cons x l)) : P l :=
list_induction_on l Hnil (take x l IH, Hcons x l)

notation `[` l:(foldr `,` (h t, cons h t) nil) `]` := l


-- Concat
-- ------

definition concat (s t : list T) : list T :=
list_rec t (fun x : T, fun l : list T, fun u : list T, cons x u) s

infixl `++` : 65 := concat

theorem nil_concat (t : list T) : nil ++ t = t := refl _

theorem cons_concat (x : T) (s t : list T) : (x :: s) ++ t = x :: (s ++ t) := refl _

theorem concat_nil (t : list T) : t ++ nil = t :=
list_induction_on t (refl _)
  (take (x : T) (l : list T) (H : concat l nil = l),
    H ▸ (refl (cons x (concat l nil))))

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

definition length : list T → ℕ := list_rec 0 (fun x l m, succ m)

-- TODO: cannot replace zero by 0
theorem length_nil : length (@nil T) = zero := refl _

theorem length_cons (x : T) (t : list T) : length (x :: t) = succ (length t) := refl _

theorem length_concat (s t : list T) : length (s ++ t) = length s + length t :=
list_induction_on s
  (calc
    length (concat nil t) = length t : refl _
      ... = zero + length t : {symm (add_zero_left (length t))}
      ... = length (@nil T) + length t : refl _)
  (take x s,
    assume H : length (concat s t) = length s + length t,
    calc
      length (concat (cons x s) t ) = succ (length (concat s t))  : refl _
	... = succ (length s + length t)  : { H }
	... = succ (length s) + length t  : {symm (add_succ_left _ _)}
	... = length (cons x s) + length t : refl _)

-- Reverse
-- -------

definition reverse : list T → list T := list_rec nil (fun x l r, r ++ [x])

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

definition append (x : T) : list T → list T := list_rec (x :: nil) (fun y l l', y :: l')

theorem append_nil (x : T) : append x nil = [x] := refl _

theorem append_cons (x : T) (y : T) (l : list T) : append x (y :: l)  = y :: (append x l) := refl _

theorem append_eq_concat  (x : T) (l : list T) : append x l = l ++ [x] :=
list_induction_on l (refl _)
  (take y l,
    assume P : append x l = concat l [x],
    P ▸ refl _)

set_option unifier.expensive false
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

exit
-- Head and tail
-- -------------

definition head (x0 : T) : list T → T := list_rec x0 (fun x l h, x)

theorem head_nil (x0 : T) : head x0 (@nil T) = x0 := refl _

theorem head_cons (x : T) (x0 : T) (t : list T) : head x0 (x :: t) = x := refl _

theorem head_concat (s t : list T) (x0 : T) : s ≠ nil → (head x0 (s ++ t) = head x0 s) :=
list_cases_on s
  (take H : nil ≠ nil, absurd_elim (head x0 (concat nil t) = head x0 nil) (refl nil) H)
  (take x s,
    take H : cons x s ≠ nil,
    calc
      head x0 (concat (cons x s) t) = head x0 (cons x (concat s t)) : {cons_concat _ _ _}
        ... = x : {head_cons _ _ _}
        ... = head x0 (cons x s) : {symm ( head_cons x x0 s)})

definition tail : list T → list T := list_rec nil (fun x l b, l)

theorem tail_nil : tail (@nil T) = nil := refl _

theorem tail_cons (x : T) (l : list T) : tail (cons x l) = l := refl _

theorem cons_head_tail (x0 : T) (l : list T) : l ≠ nil → (head x0 l) :: (tail l) = l :=
list_cases_on l
  (assume H : nil ≠ nil, absurd_elim _ (refl _) H)
  (take x l, assume H : cons x l ≠ nil, refl _)


-- List membership
-- ---------------

definition mem (x : T) : list T → Prop := list_rec false (fun y l H, x = y ∨ H)

infix `∈` : 50 := mem

theorem mem_nil (x : T) : mem x nil ↔ false := iff_refl _

theorem mem_cons (x : T) (y : T) (l : list T) : mem x (cons y l) ↔ (x = y ∨ mem x l) := iff_refl _
