----------------------------------------------------------------------------------------------------
--- Copyright (c) 2014 Parikshit Khanna. All rights reserved.
--- Released under Apache 2.0 license as described in the file LICENSE.
--- Authors: Parikshit Khanna, Jeremy Avigad
----------------------------------------------------------------------------------------------------

-- Theory list
-- ===========
--
-- Basic properties of lists.

import tools.tactic
import data.nat
import logic
-- import if -- for find

using nat
using congr
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
    show concat (cons x l) nil = cons x l, from H ▸ refl _)

theorem concat_assoc (s t u : list T) : s ++ t ++ u = s ++ (t ++ u) :=
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

theorem length_nil : length (@nil T) = 0 := refl _

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

-- add_rewrite length_nil length_cons


-- Append
-- ------

definition append (x : T) : list T → list T := list_rec [x] (fun y l l', y :: l')

theorem append_nil (x : T) : append x nil = [x] := refl _

theorem append_cons (x : T) (y : T) (l : list T) : append x (y :: l)  = y :: (append x l) := refl _

theorem append_eq_concat  (x : T) (l : list T) : append x l = l ++ [x] := refl _

-- add_rewrite append_nil append_cons


-- Reverse
-- -------

definition reverse : list T → list T := list_rec nil (fun x l r, r ++ [x])

theorem reverse_nil : reverse (@nil T) = nil := refl _

theorem reverse_cons (x : T) (l : list T) : reverse (x :: l) = append x (reverse l) := refl _

theorem reverse_singleton (x : T) : reverse [x] = [x] := refl _

theorem reverse_concat (s t : list T) : reverse (s ++ t) = (reverse t) ++ (reverse s) :=
list_induction_on s (symm (concat_nil _))
  (take x s,
    assume IH : reverse (s ++ t) = concat (reverse t) (reverse s),
    calc
      reverse ((x :: s) ++ t) = reverse (s ++ t) ++ [x] : refl _
        ... = reverse t ++ reverse s ++ [x] : {IH}
        ... = reverse t ++ (reverse s ++ [x]) : concat_assoc _ _ _
        ... = reverse t ++ (reverse (x :: s)) : refl _)

theorem reverse_reverse (l : list T) : reverse (reverse l) = l :=
list_induction_on l (refl _)
  (take x l',
    assume H: reverse (reverse l') = l',
    show reverse (reverse (x :: l')) = x :: l', from
      calc
      	reverse (reverse (x :: l')) = reverse (reverse l' ++ [x]) : refl _
          ... = reverse [x] ++ reverse (reverse l') : reverse_concat _ _
          ... = [x] ++ l' : { H }
          ... = x :: l' : refl _)

theorem append_eq_reverse_cons  (x : T) (l : list T) : append x l = reverse (x :: reverse l) :=
list_induction_on l (refl _)
  (take y l',
    assume H : append x l' = reverse (x :: reverse l'),
    calc
      append x (y :: l') = (y :: l') ++ [ x ] : append_eq_concat _ _
        ... = concat (reverse (reverse (y :: l'))) [ x ] : {symm (reverse_reverse _)}
        ... = reverse (x :: (reverse (y :: l'))) : refl _)


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

-- TODO: constructively, equality is stronger. Use that?
theorem mem_nil (x : T) : x ∈ nil ↔ false := iff_refl _

theorem mem_cons (x : T) (y : T) (l : list T) : mem x (cons y l) ↔ (x = y ∨ mem x l) := iff_refl _

theorem mem_concat_imp_or (x : T) (s t : list T) : x ∈ s ++ t → x ∈ s ∨ x ∈ t :=
list_induction_on s (or_intro_right _)
  (take y s,
    assume IH : x ∈ s ++ t → x ∈ s ∨ x ∈ t,
    assume H1 : x ∈ (y :: s) ++ t,
    have H2 : x = y ∨ x ∈ s ++ t, from H1,
    have H3 : x = y ∨ x ∈ s ∨ x ∈ t, from imp_or_right H2 IH,
    iff_elim_right (or_assoc _ _ _) H3)

theorem mem_or_imp_concat (x : T) (s t : list T) : x ∈ s ∨ x ∈ t → x ∈ s ++ t :=
list_induction_on s
  (take H, or_elim H (false_elim _) (assume H, H))
  (take y s,
    assume IH : x ∈ s ∨ x ∈ t → x ∈ s ++ t,
    assume H : x ∈ y :: s ∨ x ∈ t,
      or_elim H
        (assume H1,
          or_elim H1
            (take H2 : x = y, or_intro_left _ H2)
            (take H2 : x ∈ s, or_intro_right _ (IH (or_intro_left _ H2))))
        (assume H1 : x ∈ t, or_intro_right _ (IH (or_intro_right _ H1))))

theorem mem_concat (x : T) (s t : list T) : x ∈ s ++ t ↔ x ∈ s ∨ x ∈ t
:= iff_intro (mem_concat_imp_or _ _ _) (mem_or_imp_concat _ _ _)

theorem mem_split (x : T) (l : list T) : x ∈ l → ∃s t : list T, l = s ++ (x :: t) :=
list_induction_on l
  (take H : x ∈ nil, false_elim _ (iff_elim_left (mem_nil x) H))
  (take y l,
    assume IH : x ∈ l → ∃s t : list T, l = s ++ (x :: t),
    assume H : x ∈ y :: l,
    or_elim H
      (assume H1 : x = y,
        exists_intro nil
          (exists_intro l (subst H1 (refl _))))
      (assume H1 : x ∈ l,
        obtain s (H2 : ∃t : list T, l = s ++ (x :: t)), from IH H1,
        obtain t (H3 : l = s ++ (x :: t)), from H2,
        have H4 : y :: l = (y :: s) ++ (x :: t),
          from trans (subst H3 (refl (y :: l))) (cons_concat _ _ _),
        exists_intro _ (exists_intro _ H4)))

-- Find
-- ----

-- to do this: need decidability of = for nat
-- definition find (x : T) : list T → nat
-- := list_rec 0 (fun y l b, if x = y then 0 else succ b)

-- theorem find_nil (f : T) : find f nil = 0
-- :=refl _

-- theorem find_cons (x y : T) (l : list T) : find x (cons y l) =
--     if x = y then 0 else succ (find x l)
-- := refl _

-- theorem not_mem_find (l : list T) (x : T) : ¬ mem x l → find x l = length l
-- :=
--   @list_induction_on T (λl, ¬ mem x l → find x l = length l) l
-- --  list_induction_on l
--     (assume P1 : ¬ mem x nil,
--       show find x nil = length nil, from
--         calc
--           find x nil = 0 : find_nil _
--             ... = length nil : by simp)
--      (take y l,
--        assume IH : ¬ (mem x l) → find x l = length l,
--        assume P1 : ¬ (mem x (cons y l)),
--        have P2 : ¬ (mem x l ∨ (y = x)), from subst P1 (mem_cons _ _ _),
--        have P3 : ¬ (mem x l) ∧ (y ≠ x),from subst P2 (not_or _ _),
--        have P4 : x ≠ y, from ne_symm (and_elim_right P3),
--        calc
--           find x (cons y l) = succ (find x l) :
--               trans (find_cons _ _ _) (not_imp_if_eq P4 _ _)
--             ... = succ (length l) : {IH (and_elim_left P3)}
--             ... = length (cons y l) : symm (length_cons _ _))

-- nth element
-- -----------

definition nth (x0 : T) (l : list T) (n : ℕ) : T :=
nat_rec (λl, head x0 l) (λm f l, f (tail l)) n l

theorem nth_zero (x0 : T) (l : list T) : nth x0 l 0 = head x0 l := refl _

theorem nth_succ (x0 : T) (l : list T) (n : ℕ) : nth x0 l (succ n) = nth x0 (tail l) n := refl _

end

-- declare global notation outside the section
infixl `++` : 65 := concat
