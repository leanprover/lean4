-- Copyright (c) 2014 Floris van Doorn. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Floris van Doorn
import data.nat.basic data.empty
open nat eq.ops

inductive vector (T : Type) : ℕ → Type :=
  nil {} : vector T 0,
  cons : T → ∀{n}, vector T n → vector T (succ n)

namespace vector
  infix `::` := cons --at what level?
  notation `[` l:(foldr `,` (h t, cons h t) nil) `]` := l

  section sc_vector
  variable {T : Type}

  protected theorem rec_on {C : ∀ (n : ℕ), vector T n → Type} {n : ℕ} (v : vector T n) (Hnil : C 0 nil)
    (Hcons : ∀(x : T) {n : ℕ} (w : vector T n), C n w → C (succ n) (cons x w)) : C n v :=
  rec Hnil Hcons v

  protected theorem induction_on {C : ∀ (n : ℕ), vector T n → Prop} {n : ℕ} (v : vector T n) (Hnil : C 0 nil)
    (Hcons : ∀(x : T) {n : ℕ} (w : vector T n), C n w → C (succ n) (cons x w)) : C n v :=
  rec_on v Hnil Hcons

  protected theorem case_on {C : ∀ (n : ℕ), vector T n → Type} {n : ℕ} (v : vector T n) (Hnil : C 0 nil)
    (Hcons : ∀(x : T) {n : ℕ} (w : vector T n), C (succ n) (cons x w)) : C n v :=
  rec_on v Hnil (take x n v IH, Hcons x v)

  protected definition is_inhabited [instance] (A : Type) (H : inhabited A) (n : nat) : inhabited (vector A n) :=
  nat.rec_on n
    (inhabited.mk (@vector.nil A))
    (λ (n : nat) (iH : inhabited (vector A n)),
      inhabited.destruct H
        (λa, inhabited.destruct iH
          (λv, inhabited.mk (vector.cons a v))))

  -- TODO(Leo): mark_it_private
  theorem case_zero_lem_aux {C : vector T 0 → Type} {n : ℕ} (v : vector T n) (Hnil : C nil) :
    ∀ H : n = 0, C (cast (congr_arg (vector T) H) v) :=
  rec_on v (take H : 0 = 0, (eq.rec Hnil (cast_eq _ nil⁻¹)))
  (take (x : T) (n : ℕ) (w : vector T n) IH (H : succ n = 0),
     false.rec_type _ (absurd H !succ_ne_zero))

  theorem case_zero {C : vector T 0 → Type} (v : vector T 0) (Hnil : C nil) : C v :=
  eq.rec (case_zero_lem_aux v Hnil (eq.refl 0)) (cast_eq _ v)

  private theorem rec_nonempty_lem {C : Π{n}, vector T (succ n) → Type} {n : ℕ} (v : vector T n)
    (Hone : Πa, C [a]) (Hcons : Πa {n} (v : vector T (succ n)), C v → C (a :: v))
    : ∀{m} (H : n = succ m), C (cast (congr_arg (vector T) H) v) :=
  case_on v (take m (H : 0 = succ m), false.rec_type _ (absurd (H⁻¹) !succ_ne_zero))
    (take x n v m H,
      have H2 : C (x::v), from
        sorry,
        -- rec_on v
        --   (Hone x)
        --   (take y n w IH, Hcons x (y::w)),
      show C (cast (congr_arg (vector T) H) (x::v)), from
        sorry
    )

  theorem rec_nonempty {C : Π{n}, vector T (succ n) → Type} {n : ℕ} (v : vector T (succ n))
    (Hone : Πa, C [a]) (Hcons : Πa {n} (v : vector T (succ n)), C v → C (a :: v)) : C v :=
  sorry

  private theorem case_succ_lem {C : Π{n}, vector T (succ n) → Type} {n : ℕ} (v : vector T n)
    (H : Πa {n} (v : vector T n), C (a :: v))
    : ∀{m} (H : n = succ m), C (cast (congr_arg (vector T) H) v) :=
  sorry

  theorem case_succ {C : Π{n}, vector T (succ n) → Type} {n : ℕ} (v : vector T (succ n))
    (H : Πa {n} (v : vector T n), C (a :: v)) : C v :=
  sorry

  theorem vector0_eq_nil (v : vector T 0) : v = nil :=
  case_zero v rfl

  -- Concat
  -- ------

  definition cast_subst {A : Type} {P : A → Type} {a a' : A} (H : a = a') (B : P a) : P a' :=
  cast (congr_arg P H) B

  definition concat {n m : ℕ} (v : vector T n) (w : vector T m) : vector T (n + m) :=
  vector.rec (cast_subst (!add.zero_left⁻¹) w) (λx n w' u, cast_subst (!add.succ_left⁻¹) (x::u)) v

  infixl `++`:65 := concat

  theorem nil_concat {n : ℕ} (v : vector T n) : nil ++ v = cast_subst (!add.zero_left⁻¹) v := rfl

  theorem cons_concat {n m : ℕ} (x : T) (v : vector T n) (w : vector T m)
    : (x :: v) ++ w = cast_subst (!add.succ_left⁻¹) (x::(v++w)) := rfl

/-
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
-/

  -- Length
  -- ------

  definition length {n : ℕ} (v : vector T n) := n

  theorem length_nil : length (@nil T) = 0 := rfl

-- theorem length_cons (x : T) (t : list T) : length (x :: t) = succ (length t) := rfl

-- theorem length_concat (s t : list T) : length (s ++ t) = length s + length t :=
-- list_induction_on s
--   (calc
--     length (concat nil t) = length t   : rfl
--       ... = zero + length t            : {add_zero_left⁻¹}
--       ... = length (@nil T) + length t : rfl)
--   (take x s,
--     assume H : length (concat s t) = length s + length t,
--     calc
--       length (concat (cons x s) t ) = succ (length (concat s t))  : rfl
--         ... = succ (length s + length t)   : { H }
--         ... = succ (length s) + length t   : {add_succ_left⁻¹}
--         ... = length (cons x s) + length t : rfl)

-- -- add_rewrite length_nil length_cons


-- -- Append
-- -- ------

-- definition append (x : T) : list T → list T := list_rec [x] (fun y l l', y :: l')

-- theorem append_nil (x : T) : append x nil = [x] := refl _

-- theorem append_cons (x : T) (y : T) (l : list T) : append x (y :: l)  = y :: (append x l) := refl _

-- theorem append_eq_concat  (x : T) (l : list T) : append x l = l ++ [x] := refl _

-- -- add_rewrite append_nil append_cons


-- -- Reverse
-- -- -------

-- definition reverse : list T → list T := list_rec nil (fun x l r, r ++ [x])

-- theorem reverse_nil : reverse (@nil T) = nil := refl _

-- theorem reverse_cons (x : T) (l : list T) : reverse (x :: l) = append x (reverse l) := refl _

-- theorem reverse_singleton (x : T) : reverse [x] = [x] := refl _

-- theorem reverse_concat (s t : list T) : reverse (s ++ t) = (reverse t) ++ (reverse s) :=
-- list_induction_on s (symm (concat_nil _))
--   (take x s,
--     assume IH : reverse (s ++ t) = concat (reverse t) (reverse s),
--     calc
--       reverse ((x :: s) ++ t) = reverse (s ++ t) ++ [x] : refl _
--         ... = reverse t ++ reverse s ++ [x] : {IH}
--         ... = reverse t ++ (reverse s ++ [x]) : concat_assoc _ _ _
--         ... = reverse t ++ (reverse (x :: s)) : refl _)

-- theorem reverse_reverse (l : list T) : reverse (reverse l) = l :=
-- list_induction_on l (refl _)
--   (take x l',
--     assume H: reverse (reverse l') = l',
--     show reverse (reverse (x :: l')) = x :: l', from
--       calc
--         reverse (reverse (x :: l')) = reverse (reverse l' ++ [x]) : refl _
--           ... = reverse [x] ++ reverse (reverse l') : reverse_concat _ _
--           ... = [x] ++ l' : { H }
--           ... = x :: l' : refl _)

-- theorem append_eq_reverse_cons  (x : T) (l : list T) : append x l = reverse (x :: reverse l) :=
-- list_induction_on l (refl _)
--   (take y l',
--     assume H : append x l' = reverse (x :: reverse l'),
--     calc
--       append x (y :: l') = (y :: l') ++ [ x ] : append_eq_concat _ _
--         ... = concat (reverse (reverse (y :: l'))) [ x ] : {symm (reverse_reverse _)}
--         ... = reverse (x :: (reverse (y :: l'))) : refl _)


-- -- Head and tail
-- -- -------------

-- definition head (x0 : T) : list T → T := list_rec x0 (fun x l h, x)

-- theorem head_nil (x0 : T) : head x0 (@nil T) = x0 := refl _

-- theorem head_cons (x : T) (x0 : T) (t : list T) : head x0 (x :: t) = x := refl _

-- theorem head_concat (s t : list T) (x0 : T) : s ≠ nil → (head x0 (s ++ t) = head x0 s) :=
-- list_cases_on s
--   (take H : nil ≠ nil, absurd (refl nil) H)
--   (take x s,
--     take H : cons x s ≠ nil,
--     calc
--       head x0 (concat (cons x s) t) = head x0 (cons x (concat s t)) : {cons_concat _ _ _}
--         ... = x : {head_cons _ _ _}
--         ... = head x0 (cons x s) : {symm ( head_cons x x0 s)})

-- definition tail : list T → list T := list_rec nil (fun x l b, l)

-- theorem tail_nil : tail (@nil T) = nil := refl _

-- theorem tail_cons (x : T) (l : list T) : tail (cons x l) = l := refl _

-- theorem cons_head_tail (x0 : T) (l : list T) : l ≠ nil → (head x0 l) :: (tail l) = l :=
-- list_cases_on l
--   (assume H : nil ≠ nil, absurd (refl _) H)
--   (take x l, assume H : cons x l ≠ nil, refl _)


-- -- List membership
-- -- ---------------

-- definition mem (x : T) : list T → Prop := list_rec false (fun y l H, x = y ∨ H)

-- infix `∈` := mem

-- -- TODO: constructively, equality is stronger. Use that?
-- theorem mem_nil (x : T) : x ∈ nil ↔ false := iff_refl _

-- theorem mem_cons (x : T) (y : T) (l : list T) : mem x (cons y l) ↔ (x = y ∨ mem x l) := iff_refl _

-- theorem mem_concat_imp_or (x : T) (s t : list T) : x ∈ s ++ t → x ∈ s ∨ x ∈ t :=
-- list_induction_on s or_inr
--   (take y s,
--     assume IH : x ∈ s ++ t → x ∈ s ∨ x ∈ t,
--     assume H1 : x ∈ (y :: s) ++ t,
--     have H2 : x = y ∨ x ∈ s ++ t, from H1,
--     have H3 : x = y ∨ x ∈ s ∨ x ∈ t, from or_imp_or_right H2 IH,
--     iff_elim_right or_assoc H3)

-- theorem mem_or_imp_concat (x : T) (s t : list T) : x ∈ s ∨ x ∈ t → x ∈ s ++ t :=
-- list_induction_on s
--   (take H, or_elim H (false_elim _) (assume H, H))
--   (take y s,
--     assume IH : x ∈ s ∨ x ∈ t → x ∈ s ++ t,
--     assume H : x ∈ y :: s ∨ x ∈ t,
--       or_elim H
--         (assume H1,
--           or_elim H1
--             (take H2 : x = y, or_inl H2)
--             (take H2 : x ∈ s, or_inr (IH (or_inl H2))))
--         (assume H1 : x ∈ t, or_inr (IH (or_inr H1))))

-- theorem mem_concat (x : T) (s t : list T) : x ∈ s ++ t ↔ x ∈ s ∨ x ∈ t
-- := iff_intro (mem_concat_imp_or _ _ _) (mem_or_imp_concat _ _ _)

-- theorem mem_split (x : T) (l : list T) : x ∈ l → ∃s t : list T, l = s ++ (x :: t) :=
-- list_induction_on l
--   (take H : x ∈ nil, false_elim _ (iff_elim_left (mem_nil x) H))
--   (take y l,
--     assume IH : x ∈ l → ∃s t : list T, l = s ++ (x :: t),
--     assume H : x ∈ y :: l,
--     or_elim H
--       (assume H1 : x = y,
--         exists_intro nil
--           (exists_intro l (subst H1 (refl _))))
--       (assume H1 : x ∈ l,
--         obtain s (H2 : ∃t : list T, l = s ++ (x :: t)), from IH H1,
--         obtain t (H3 : l = s ++ (x :: t)), from H2,
--         have H4 : y :: l = (y :: s) ++ (x :: t),
--           from subst H3 (refl (y :: l)),
--         exists_intro _ (exists_intro _ H4)))

-- -- Find
-- -- ----

-- -- to do this: need decidability of = for nat
-- -- definition find (x : T) : list T → nat
-- -- := list_rec 0 (fun y l b, if x = y then 0 else succ b)

-- -- theorem find_nil (f : T) : find f nil = 0
-- -- :=refl _

-- -- theorem find_cons (x y : T) (l : list T) : find x (cons y l) =
-- --     if x = y then 0 else succ (find x l)
-- -- := refl _

-- -- theorem not_mem_find (l : list T) (x : T) : ¬ mem x l → find x l = length l
-- -- :=
-- --   @list_induction_on T (λl, ¬ mem x l → find x l = length l) l
-- -- --  list_induction_on l
-- --     (assume P1 : ¬ mem x nil,
-- --       show find x nil = length nil, from
-- --         calc
-- --           find x nil = 0 : find_nil _
-- --             ... = length nil : by simp)
-- --      (take y l,
-- --        assume IH : ¬ (mem x l) → find x l = length l,
-- --        assume P1 : ¬ (mem x (cons y l)),
-- --        have P2 : ¬ (mem x l ∨ (y = x)), from subst P1 (mem_cons _ _ _),
-- --        have P3 : ¬ (mem x l) ∧ (y ≠ x),from subst P2 (not_or _ _),
-- --        have P4 : x ≠ y, from ne_symm (and_elim_right P3),
-- --        calc
-- --           find x (cons y l) = succ (find x l) :
-- --               trans (find_cons _ _ _) (not_imp_if_eq P4 _ _)
-- --             ... = succ (length l) : {IH (and_elim_left P3)}
-- --             ... = length (cons y l) : symm (length_cons _ _))

-- -- nth element
-- -- -----------

-- definition nth (x0 : T) (l : list T) (n : ℕ) : T :=
-- nat_rec (λl, head x0 l) (λm f l, f (tail l)) n l

-- theorem nth_zero (x0 : T) (l : list T) : nth x0 l 0 = head x0 l := refl _

-- theorem nth_succ (x0 : T) (l : list T) (n : ℕ) : nth x0 l (succ n) = nth x0 (tail l) n := refl _

  end sc_vector
  infixl `++`:65 := concat
end vector
