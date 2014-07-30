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

using nat
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
notation `[` `]` := nil
-- TODO: should this be needed?
notation `[` x `]` := cons x nil


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

-- TODO: these work:
--      calc
--        concat (cons x l) nil = cons x (concat l nil) : refl (concat (cons x l) nil)
--          ... = cons x l : {H})

--      H ▸ (refl (cons x (concat l nil))))

-- doesn't work:
--      H ▸ (refl (concat (cons x l) nil)))

theorem concat_assoc (s t u : list T) : s ++ t ++ u = s ++ (t ++ u) :=
list_induction_on s (refl _)
  (take x l,
    assume H : concat (concat l t) u = concat l (concat t u),
    calc
      concat (concat (cons x l) t) u = cons x (concat (concat l t) u) : refl _
        ... = cons x (concat l (concat t u)) : { H }
        ... = concat (cons x l) (concat t u) : refl _)

-- TODO: deleting refl doesn't work, nor does
-- H ▸ refl _)

--      concat (concat (cons x l) t) u = cons x (concat (concat l t) u) : refl _
--        ... = concat (cons x l) (concat t u) : { H })

--      concat (concat (cons x l) t) u = cons x (concat l (concat t u)) : { H }
--        ... = concat (cons x l) (concat t u) : refl _)

--      concat (concat (cons x l) t) u = cons x (concat (concat l t) u) : refl _
--        ... = cons x (concat l (concat t u)) : { H }
--        ... = concat (cons x l) (concat t u) : refl _)

-- add_rewrite nil_concat cons_concat concat_nil concat_assoc


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

-- -- add_rewrite length_nil length_cons


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

theorem reverse_reverse (l : list T) : reverse (reverse l) = l :=
list_induction_on l (refl _)
  (take x l',
    assume H: reverse (reverse l') = l',
    show reverse (reverse (cons x l')) = cons x l', from
      calc
      	reverse (reverse (cons x l')) =
            concat (reverse (cons x nil)) (reverse (reverse l')) : {reverse_concat _ _}
      	  ... = cons x l' : {H})

      -- longer versions:

      -- reverse (reverse (cons x l)) =
      --     concat (reverse (cons x nil)) (reverse (reverse l)) : {reverse_concat _ _}
      --   ... = concat (reverse (cons x nil)) l : {H}
      --   ... = cons x l : refl _)

      -- calc
      -- 	reverse (reverse (cons x l)) = reverse (concat (reverse l) (cons x nil))
      -- 	    : refl _
      -- 	  ... = concat (reverse (cons x nil)) (reverse (reverse l)) : {reverse_concat _ _}
      -- 	  ... = concat (reverse (cons x nil)) l : {H}
      -- 	  ... = cons x l : refl _)

      -- before:
      -- calc
      -- 	reverse (reverse (cons x l)) = reverse (concat (reverse l) (cons x nil))
      -- 	    : {reverse_cons x l}
      -- 	  ... = concat (reverse (cons x nil)) (reverse (reverse l)) : {reverse_concat _ _}
      -- 	  ... = concat (reverse (cons x nil)) l : {H}
      -- 	  ... = concat (concat (reverse nil) (cons x nil)) l : {reverse_cons _ _}
      -- 	  ... = concat (concat nil (cons x nil)) l : {reverse_nil}
      -- 	  ... = concat (cons x nil) l : {nil_concat _}
      -- 	  ... = cons x (concat nil l) : cons_concat _ _ _
      -- 	  ... = cons x l : {nil_concat _})


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

     -- calc
     --   append x (cons y l) = concat (cons y l) (cons x nil) : { P })

     -- calc
     --   append x (cons y l) = cons y (concat l (cons x nil)) : { P }
     --     ... = concat (cons y l) (cons x nil) : refl _)

       -- here it works!
       -- append x (cons y l) = cons y (append x l) : refl _
       -- 	 ... = cons y (concat l (cons x nil)) : { P }
       -- 	 ... = concat (cons y l) (cons x nil) : refl _)

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

definition mem (f : T) : list T → Prop := list_rec false (fun x l H, (H ∨ (x = f)))

infix `∈` : 50 := mem

theorem mem_nil (f : T) : mem f nil ↔ false := iff_refl _

theorem mem_cons (x : T) (f : T) (l : list T) : mem f (cons x l) ↔ (mem f l ∨ x = f) := iff_refl _

-- TODO: fix this!
-- theorem or_right_comm : ∀a b c, (a ∨ b) ∨ c ↔ (a ∨ c) ∨ b :=
-- take a b c, calc
--   (a ∨ b) ∨ c ↔ a ∨ (b ∨ c) : or_assoc _ _ _
--     ... ↔ a ∨ (c ∨ b) : {or_comm _ _}
--     ... ↔ (a ∨ c) ∨ b : (or_assoc _ _ _)⁻¹

-- theorem mem_concat_imp_or (f : T) (s t : list T) : mem f (concat s t) → mem f s ∨ mem f t :=
-- list_induction_on s
--   (assume H : mem f (concat nil t),
--     have H1 : mem f t, from subst H (nil_concat t),
--     show mem f nil ∨ mem f t, from or_intro_right _ H1)
--   (take x l,
--     assume IH : mem f (concat l t) → mem f l ∨ mem f t,
--     assume H : mem f (concat (cons x l) t),
--     have H1 : mem f (cons x (concat l t)), from subst H (cons_concat _ _ _),
--     have H2 : mem f (concat l t) ∨ x = f, from (mem_cons _ _ _) ◂ H1,
--     have H3 : (mem f l ∨ mem f t) ∨ x = f, from imp_or_left H2 IH,
--     have H4 : (mem f l ∨ x = f) ∨ mem f t, from or_right_comm _ _ _ ◂ H3,
--     show mem f (cons x l) ∨ mem f t, from subst H4 (symm (mem_cons _ _ _)))

-- theorem mem_or_imp_concat (f : T) (s t : list T) :
--   mem f s ∨ mem f t → mem f (concat s t)
-- :=
--   list_induction_on s
--     (assume H : mem f nil ∨ mem f t,
--       have H1 : false ∨ mem f t, from subst H (mem_nil f),
--       have H2 : mem f t, from subst H1 (or_false_right _),
--       show mem f (concat nil t), from subst H2 (symm (nil_concat _)))
--     (take x l,
--       assume IH : mem f l ∨ mem f t → mem f (concat l t),
--       assume H : (mem f (cons x l)) ∨ (mem f t),
--       have H1 : ((mem f l) ∨ (x = f)) ∨ (mem f t), from subst H (mem_cons _ _ _),
--       have H2 : (mem f t) ∨ ((mem f l) ∨ (x = f)), from subst H1 (or_comm _ _),
--       have H3 : ((mem f t) ∨ (mem f l)) ∨ (x = f), from subst H2 (symm (or_assoc _ _ _)),
--       have H4 : ((mem f l) ∨ (mem f t)) ∨ (x = f), from subst H3 (or_comm _ _),
--       have H5 : (mem f (concat l t)) ∨ (x = f), from  (or_imp_or_left H4 IH),
--       have H6 : (mem f (cons x (concat l t))), from subst H5 (symm (mem_cons _ _ _)),
--       show  (mem f (concat (cons x l) t)), from subst H6 (symm (cons_concat _ _ _)))

-- theorem mem_concat (f : T) (s t : list T) : mem f (concat s t) ↔ mem f s ∨ mem f t
-- := iff_intro (mem_concat_imp_or _ _ _) (mem_or_imp_concat _ _ _)

-- theorem mem_split (f : T) (s : list T) :
--     mem f s → ∃ a b : list T, s = concat a (cons f b)
-- :=
--   list_induction_on s
--     (assume H : mem f nil,
--       have H1  : mem f nil ↔ false, from (mem_nil f),
--       show ∃ a b : list T, nil = concat a (cons f b), from absurd_elim _ H (eqf_elim H1))
--     (take x l,
--       assume P1 : mem f l → ∃ a b : list T, l = concat a (cons f b),
--       assume P2 : mem f (cons x l),
--       have P3 : mem f l ∨ x = f, from subst P2 (mem_cons _ _ _),
--       show ∃ a b : list T, cons x l = concat a (cons f b), from
--         or_elim P3
--           (assume Q1 : mem f l,
--             obtain (a : list T) (PQ : ∃ b, l = concat a (cons f b)), from P1 Q1,
--             obtain (b : list T) (RS : l = concat a (cons f b)), from PQ,
--             exists_intro (cons x a)
--               (exists_intro b
--                 (calc
--                   cons x l = cons x (concat a (cons f b)) : { RS }
--                     ... = concat (cons x a) (cons f b) : (symm (cons_concat _ _ _)))))
--           (assume Q2 : x = f,
--             exists_intro nil
--               (exists_intro l
--                 (calc
--                   cons x l = concat nil (cons x l) : (symm (nil_concat _))
--                     ... = concat nil (cons f l) : {Q2}))))

-- -- Find
-- -- ----

-- definition find (x : T) : list T → ℕ
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

-- -- nth element
-- -- -----------

-- definition nth (x0 : T) (l : list T) (n : ℕ) : T
-- := nat.rec (λl, head x0 l) (λm f l, f (tail l)) n l

-- theorem nth (x0 : T) (l : list T) : nth_element x0 l 0 = head x0 l
-- := hcongr1 (nat::rec_zero _ _) l

-- theorem nth_element_succ (x0 : T) (l : list T) (n : ℕ) :
--     nth_element x0 l (succ n) = nth_element x0 (tail l) n
-- := hcongr1 (nat::rec_succ _ _ _) l

-- end
