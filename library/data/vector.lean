-- Copyright (c) 2014 Floris van Doorn. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Floris van Doorn, Leonardo de Moura
import data.nat.basic data.empty data.prod
open nat eq.ops prod

inductive vector (T : Type) : ℕ → Type :=
  nil {} : vector T 0,
  cons : T → ∀{n}, vector T n → vector T (succ n)

namespace vector
  notation a :: b := cons a b
  notation `[` l:(foldr `,` (h t, cons h t) nil) `]` := l

  section sc_vector
  variable {T : Type}

  protected definition is_inhabited [instance] (A : Type) (H : inhabited A) (n : nat) : inhabited (vector A n) :=
  nat.rec_on n
    (inhabited.mk nil)
    (λ (n : nat) (iH : inhabited (vector A n)),
      inhabited.destruct H
        (λa, inhabited.destruct iH
          (λv, inhabited.mk (a :: v))))

  theorem z_cases_on {A : Type} {C : vector A 0 → Type} (v : vector A 0) (Hnil : C nil) : C v :=
  have aux : ∀ (n₁ : nat) (v₁ : vector A n₁) (eq₁ : n₁ = 0) (eq₂ : v₁ == v) (Hnil : C nil), C v, from
    λ n₁ v₁, vector.rec_on v₁
      (λ (eq₁ : 0 = 0) (eq₂ : nil == v) (Hnil : C nil), eq.rec_on (heq.to_eq eq₂) Hnil)
      (λ h₂ n₂ v₂ ih eq₁ eq₂ hnil, nat.no_confusion eq₁),
  aux 0 v rfl !heq.refl Hnil

  theorem vector0_eq_nil (v : vector T 0) : v = nil :=
  z_cases_on v rfl

  protected definition destruct {A : Type} {n : nat} (v : vector A (succ n)) {P : Π {n : nat}, vector A (succ n) → Type}
                      (H : Π {n : nat} (h : A) (t : vector A n), P (h :: t)) : P v :=
  have aux : ∀ (n₁ : nat) (v₁ : vector A n₁) (eq₁ : n₁ = succ n) (eq₂ : v₁ == v), P v, from
    (λ n₁ v₁, vector.rec_on v₁
       (λ eq₁, nat.no_confusion eq₁)
       (λ h₂ n₂ v₂ ih eq₁ eq₂,
          nat.no_confusion eq₁ (λ e₃ : n₂ = n,
            have aux : Π (n₂ : nat) (e₃ : n₂ = n) (v₂ : vector A n₂) (eq₂ : h₂ :: v₂ == v), P v, from
              λ n₂ e₃, eq.rec_on (eq.rec_on e₃ rfl)
                (λ (v₂ : vector A n) (eq₂ : h₂ :: v₂ == v),
                  have Phv : P (h₂ :: v₂), from H h₂ v₂,
                  eq.rec_on (heq.to_eq eq₂) Phv),
            aux n₂ e₃ v₂ eq₂))),
  aux (succ n) v rfl !heq.refl

  definition nz_cases_on := @destruct

  definition head {A : Type} {n : nat} (v : vector A (succ n)) : A :=
  destruct v (λ n h t, h)

  definition tail {A : Type} {n : nat} (v : vector A (succ n)) : vector A n :=
  destruct v (λ n h t, t)

  example (A : Type) (n : nat) (h : A) (t : vector A n) : head (h :: t) :: tail (h :: t) = h :: t :=
  rfl

  theorem head_cons {A : Type} {n : nat} (h : A) (t : vector A n) : head (h :: t) = h :=
  rfl

  theorem tail_cons {A : Type} {n : nat} (h : A) (t : vector A n) : tail (h :: t) = t :=
  rfl

  theorem eta {A : Type} {n : nat} (v : vector A (succ n)) : head v :: tail v = v :=
  -- TODO(Leo): replace 'head_cons h t ▸ tail_cons h t ▸ rfl' with rfl
  -- after issue #318 is fixed
  destruct v (λ n h t, head_cons h t ▸ tail_cons h t ▸ rfl)

  definition last {A : Type} {n : nat} : vector A (succ n) → A :=
  nat.rec_on n
    (λ (v : vector A (succ zero)), head v)
    (λ n₁ r v, r (tail v))

  theorem last_singleton {A : Type} (a : A) : last (a :: nil) = a :=
  rfl

  theorem last_cons {A : Type} {n} (a : A) (v : vector A (succ n)) : last (a :: v) = last v :=
  rfl

  definition const {A : Type} (n : nat) (a : A) : vector A n :=
  nat.rec_on n
    nil
    (λ n₁ r, a :: r)

  theorem head_const {A : Type} (n : nat) (a : A) : head (const (succ n) a) = a :=
  rfl

  theorem last_const {A : Type} (n : nat) (a : A) : last (const (succ n) a) = a :=
  nat.induction_on n
    rfl
    (λ n₁ ih, ih)

  definition map {A B : Type} {n : nat} (f : A → B) (v : vector A n) : vector B n :=
  nat.rec_on n
    (λ v, nil)
    (λ n₁ r v, f (head v) :: r (tail v))
    v

  theorem map_vnil {A B : Type} {n : nat} (f : A → B) : map f nil = nil :=
  rfl

  theorem map_vcons {A B : Type} {n : nat} (f : A → B) (h : A) (t : vector A n) : map f (h :: t) =  f h :: map f t :=
  rfl

  definition map2 {A B C : Type} {n : nat} (f : A → B → C) (v₁ : vector A n) (v₂ : vector B n) : vector C n :=
  nat.rec_on n
    (λ v₁ v₂, nil)
    (λ n₁ r v₁ v₂, f (head v₁) (head v₂) :: r (tail v₁) (tail v₂))
    v₁ v₂

  theorem map2_vnil {A B C : Type} {n : nat} (f : A → B → C) : map2 f nil nil = nil :=
  rfl

  theorem map2_vcons {A B C : Type} {n : nat} (f : A → B → C) (h₁ : A) (h₂ : B) (t₁ : vector A n) (t₂ : vector B n) :
                     map2 f (h₁ :: t₁) (h₂ :: t₂) = f h₁ h₂ :: map2 f t₁ t₂ :=
  rfl

  definition append_core {A : Type} {n m : nat} (w : vector A m) (v : vector A n) : vector A (n + m) :=
  rec_on w
    v
    (λ (a₁ : A) (m₁ : nat) (v₁ : vector A m₁) (r₁ : vector A (n + m₁)), a₁ :: r₁)

  theorem append_vnil {A : Type} {n : nat} (v : vector A n) : append_core nil v = v :=
  rfl

  theorem append_vcons {A : Type} {n m : nat} (h : A) (t : vector A n) (v : vector A m) :
    append_core (h :: t) v = h :: (append_core t v) :=
  rfl

  definition append {A : Type} {n m : nat} (w : vector A n) (v : vector A m) : vector A (n + m) :=
  eq.rec_on !add.comm (append_core w v)

  example : append (1 :: 2 :: nil) (3 :: nil) = 1 :: 2 :: 3 :: nil :=
  rfl

  definition unzip {A B : Type} {n : nat} : vector (A × B) n → vector A n × vector B n :=
  nat.rec_on n
    (λ v, (nil, nil))
    (λ a r v,
      let t := r (tail v) in
      (pr₁ (head v) :: pr₁ t, pr₂ (head v) :: pr₂ t))

  definition zip {A B : Type} {n : nat} : vector A n → vector B n → vector (A × B) n :=
  nat.rec_on n
    (λ v₁ v₂, nil)
    (λ a r v₁ v₂, (head v₁, head v₂) :: r (tail v₁) (tail v₂))

  theorem unzip_zip {A B : Type} {n : nat} : ∀ (v₁ : vector A n) (v₂ : vector B n), unzip (zip v₁ v₂) = (v₁, v₂) :=
  nat.induction_on n
    (λ (v₁ : vector A zero) (v₂ : vector B zero),
       z_cases_on v₁ (z_cases_on v₂ rfl))
    (λ (n₁ : nat) (ih : ∀ (v₁ : vector A n₁) (v₂ : vector B n₁), unzip (zip v₁ v₂) = (v₁, v₂))
       (v₁ : vector A (succ n₁)) (v₂ : vector B (succ n₁)), calc
       unzip (zip v₁ v₂) = unzip ((head v₁, head v₂) :: zip (tail v₁) (tail v₂)) : rfl
                     ... = (head v₁ :: pr₁ (unzip (zip (tail v₁) (tail v₂))),
                            head v₂ :: pr₂ (unzip (zip (tail v₁) (tail v₂))))    : rfl
                     ... = (head v₁ :: pr₁ (tail v₁, tail v₂),
                            head v₂ :: pr₂ (tail v₁, tail v₂))                   : ih
                     ... = (head v₁ :: tail v₁, head v₂ :: tail v₂)              : rfl
                     ... = (v₁, head v₂ :: tail v₂)                              : vector.eta
                     ... = (v₁, v₂)                                              : vector.eta)

  theorem zip_unzip {A B : Type} {n : nat} : ∀ (v : vector (A × B) n), zip (pr₁ (unzip v)) (pr₂ (unzip v)) = v :=
  nat.induction_on n
    (λ (v : vector (A × B) zero),
       z_cases_on v rfl)
    (λ (n₁ : nat) (ih : ∀ v, zip (pr₁ (unzip v)) (pr₂ (unzip v)) = v) (v : vector (A × B) (succ n₁)), calc
       zip (pr₁ (unzip v)) (pr₂ (unzip v)) = zip (pr₁ (head v) :: pr₁ (unzip (tail v)))
                                                 (pr₂ (head v) :: pr₂ (unzip (tail v)))                  : rfl
                 ... = (pr₁ (head v), pr₂ (head v)) :: zip (pr₁ (unzip (tail v))) (pr₂ (unzip (tail v))) : rfl
                 ... = (pr₁ (head v), pr₂ (head v)) :: tail v                                            : ih
                 ... = head v :: tail v                                                                  : prod.eta
                 ... = v                                                                                 : vector.eta)


  section
    universe variables l₁ l₂
    variable {A : Type.{l₁}}
    variable {C : Π (n : nat), vector A n → Type.{l₂+1}}
    definition brec_on {n : nat} (v : vector A n) (H : Π (n : nat) (v : vector A n), @below A C n v → C n v) : C n v :=
    have general : C n v × @below A C n v, from
      rec_on v
       (pair (H zero nil unit.star) unit.star)
       (λ (a₁ : A) (n₁ : nat) (v₁ : vector A n₁) (r₁ : C n₁ v₁ × @below A C n₁ v₁),
          have b : @below A C _ (a₁ :: v₁), from
            r₁,
          have c : C (succ n₁) (a₁ :: v₁), from
            H (succ n₁) (a₁ :: v₁) b,
          pair c b),
    pr₁ general
  end

  -- STOPPED HERE


  private theorem rec_nonempty_lem {C : Π{n}, vector T (succ n) → Type} {n : ℕ} (v : vector T n)
    (Hone : Πa, C [a]) (Hcons : Πa {n} (v : vector T (succ n)), C v → C (a :: v))
    : ∀{m} (H : n = succ m), C (cast (congr_arg (vector T) H) v) :=
  cases_on v (take m (H : 0 = succ m), false.rec _ (absurd (H⁻¹) !succ_ne_zero))
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

  -- Concat
  -- ------

  definition cast_subst {A : Type} {P : A → Type} {a a' : A} (H : a = a') (B : P a) : P a' :=
  cast (congr_arg P H) B

  definition concat {n m : ℕ} (v : vector T n) (w : vector T m) : vector T (n + m) :=
  vector.rec (cast_subst (!add.zero_left⁻¹) w) (λx n w' u, cast_subst (!add.succ_left⁻¹) (x::u)) v

  notation h ++ t := concat h t

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
  notation a ++ b := concat a b
end vector
