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
import logic tools.helper_tactics
-- import if -- for find

using nat
using eq_ops
using helper_tactics

namespace list

-- Type
-- ----

inductive list (T : Type) : Type :=
nil {} : list T,
cons   : T → list T → list T

infix `::` := cons

section

variable {T : Type}

theorem induction_on [protected] {P : list T → Prop} (l : list T) (Hnil : P nil)
    (Hind : forall x : T, forall l : list T, forall H : P l, P (cons x l)) : P l :=
list_rec Hnil Hind l

theorem cases_on [protected] {P : list T → Prop} (l : list T) (Hnil : P nil)
    (Hcons : forall x : T, forall l : list T, P (cons x l)) : P l :=
induction_on l Hnil (take x l IH, Hcons x l)

notation `[` l:(foldr `,` (h t, cons h t) nil) `]` := l


-- Concat
-- ------

definition concat (s t : list T) : list T :=
list_rec t (fun x : T, fun l : list T, fun u : list T, cons x u) s

infixl `++` : 65 := concat

theorem nil_concat {t : list T} : nil ++ t = t

theorem cons_concat {x : T} {s t : list T} : (x :: s) ++ t = x :: (s ++ t)

theorem concat_nil {t : list T} : t ++ nil = t :=
induction_on t rfl
  (take (x : T) (l : list T) (H : concat l nil = l),
    show concat (cons x l) nil = cons x l, from H ▸ rfl)

theorem concat_assoc {s t u : list T} : s ++ t ++ u = s ++ (t ++ u) :=
induction_on s rfl
  (take x l,
    assume H : concat (concat l t) u = concat l (concat t u),
    calc
      concat (concat (cons x l) t) u = cons x (concat (concat l t) u) : rfl
        ... = cons x (concat l (concat t u))                          : {H}
        ... = concat (cons x l) (concat t u)                          : rfl)

-- Length
-- ------

definition length : list T → ℕ := list_rec 0 (fun x l m, succ m)

theorem length_nil : length (@nil T) = 0 := rfl

theorem length_cons {x : T} {t : list T} : length (x :: t) = succ (length t)

theorem length_concat {s t : list T} : length (s ++ t) = length s + length t :=
induction_on s
  (calc
    length (concat nil t) = length t   : rfl
      ... = zero + length t            : {add_zero_left⁻¹}
      ... = length (@nil T) + length t : rfl)
  (take x s,
    assume H : length (concat s t) = length s + length t,
    calc
      length (concat (cons x s) t ) = succ (length (concat s t))  : rfl
        ... = succ (length s + length t)   : {H}
        ... = succ (length s) + length t   : {add_succ_left⁻¹}
        ... = length (cons x s) + length t : rfl)

-- add_rewrite length_nil length_cons

-- Append
-- ------

definition append (x : T) : list T → list T := list_rec [x] (fun y l l', y :: l')

theorem append_nil {x : T} : append x nil = [x]

theorem append_cons {x y : T} {l : list T} : append x (y :: l)  = y :: (append x l)

theorem append_eq_concat  {x : T} {l : list T} : append x l = l ++ [x]

-- add_rewrite append_nil append_cons

-- Reverse
-- -------

definition reverse : list T → list T := list_rec nil (fun x l r, r ++ [x])

theorem reverse_nil : reverse (@nil T) = nil

theorem reverse_cons {x : T} {l : list T} : reverse (x :: l) = append x (reverse l)

theorem reverse_singleton {x : T} : reverse [x] = [x]

theorem reverse_concat {s t : list T} : reverse (s ++ t) = (reverse t) ++ (reverse s) :=
induction_on s (concat_nil⁻¹)
  (take x s,
    assume IH : reverse (s ++ t) = concat (reverse t) (reverse s),
    calc
      reverse ((x :: s) ++ t) = reverse (s ++ t) ++ [x] : rfl
        ... = reverse t ++ reverse s ++ [x]             : {IH}
        ... = reverse t ++ (reverse s ++ [x])           : concat_assoc
        ... = reverse t ++ (reverse (x :: s))           : rfl)

theorem reverse_reverse {l : list T} : reverse (reverse l) = l :=
induction_on l rfl
  (take x l',
    assume H: reverse (reverse l') = l',
    show reverse (reverse (x :: l')) = x :: l', from
      calc
        reverse (reverse (x :: l')) = reverse (reverse l' ++ [x]) : rfl
          ... = reverse [x] ++ reverse (reverse l')               : reverse_concat
          ... = [x] ++ l'                                         : {H}
          ... = x :: l'                                           : rfl)

theorem append_eq_reverse_cons  {x : T} {l : list T} : append x l = reverse (x :: reverse l) :=
induction_on l rfl
  (take y l',
    assume H : append x l' = reverse (x :: reverse l'),
    calc
      append x (y :: l') = (y :: l') ++ [ x ]            : append_eq_concat
        ... = concat (reverse (reverse (y :: l'))) [ x ] : {reverse_reverse⁻¹}
        ... = reverse (x :: (reverse (y :: l')))         : rfl)


-- Head and tail
-- -------------

definition head (x : T) : list T → T := list_rec x (fun x l h, x)

theorem head_nil {x : T} : head x (@nil T) = x

theorem head_cons {x x' : T} {t : list T} : head x' (x :: t) = x

theorem head_concat {s t : list T} {x : T} : s ≠ nil → (head x (s ++ t) = head x s) :=
cases_on s
  (take H : nil ≠ nil, absurd rfl H)
  (take x s, take H : cons x s ≠ nil,
    calc
      head x (concat (cons x s) t) = head x (cons x (concat s t)) : {cons_concat}
        ... = x                                                   : {head_cons}
        ... = head x (cons x s)                                   : {head_cons⁻¹})

definition tail : list T → list T := list_rec nil (fun x l b, l)

theorem tail_nil : tail (@nil T) = nil

theorem tail_cons {x : T} {l : list T} : tail (cons x l) = l

theorem cons_head_tail {x : T} {l : list T} : l ≠ nil → (head x l) :: (tail l) = l :=
cases_on l
  (assume H : nil ≠ nil, absurd rfl H)
  (take x l, assume H : cons x l ≠ nil, rfl)

-- List membership
-- ---------------

definition mem (x : T) : list T → Prop := list_rec false (fun y l H, x = y ∨ H)

infix `∈` := mem

-- TODO: constructively, equality is stronger. Use that?
theorem mem_nil {x : T} : x ∈ nil ↔ false := iff_rfl

theorem mem_cons {x y : T} {l : list T} : mem x (cons y l) ↔ (x = y ∨ mem x l) := iff_rfl

theorem mem_concat_imp_or {x : T} {s t : list T} : x ∈ s ++ t → x ∈ s ∨ x ∈ t :=
induction_on s or_inr
  (take y s,
    assume IH : x ∈ s ++ t → x ∈ s ∨ x ∈ t,
    assume H1 : x ∈ (y :: s) ++ t,
    have H2 : x = y ∨ x ∈ s ++ t, from H1,
    have H3 : x = y ∨ x ∈ s ∨ x ∈ t, from or_imp_or_right H2 IH,
    iff_elim_right or_assoc H3)

theorem mem_or_imp_concat {x : T} {s t : list T} : x ∈ s ∨ x ∈ t → x ∈ s ++ t :=
induction_on s
  (take H, or_elim H false_elim (assume H, H))
  (take y s,
    assume IH : x ∈ s ∨ x ∈ t → x ∈ s ++ t,
    assume H : x ∈ y :: s ∨ x ∈ t,
      or_elim H
        (assume H1,
          or_elim H1
            (take H2 : x = y, or_inl H2)
            (take H2 : x ∈ s, or_inr (IH (or_inl H2))))
        (assume H1 : x ∈ t, or_inr (IH (or_inr H1))))

theorem mem_concat {x : T} {s t : list T} : x ∈ s ++ t ↔ x ∈ s ∨ x ∈ t
:= iff_intro mem_concat_imp_or mem_or_imp_concat

theorem mem_split {x : T} {l : list T} : x ∈ l → ∃s t : list T, l = s ++ (x :: t) :=
induction_on l
  (take H : x ∈ nil, false_elim (iff_elim_left mem_nil H))
  (take y l,
    assume IH : x ∈ l → ∃s t : list T, l = s ++ (x :: t),
    assume H : x ∈ y :: l,
    or_elim H
      (assume H1 : x = y,
        exists_intro nil
          (exists_intro l (subst H1 rfl)))
      (assume H1 : x ∈ l,
        obtain s (H2 : ∃t : list T, l = s ++ (x :: t)), from IH H1,
        obtain t (H3 : l = s ++ (x :: t)), from H2,
        have H4 : y :: l = (y :: s) ++ (x :: t),
          from subst H3 rfl,
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
--   @induction_on T (λl, ¬ mem x l → find x l = length l) l
-- --  induction_on l
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

definition nth (x : T) (l : list T) (n : ℕ) : T :=
nat_rec (λl, head x l) (λm f l, f (tail l)) n l

theorem nth_zero {x : T} {l : list T} : nth x l 0 = head x l

theorem nth_succ {x : T} {l : list T} {n : ℕ} : nth x l (succ n) = nth x (tail l) n

end

-- declare global notation outside the section
infixl `++` := concat

end list
