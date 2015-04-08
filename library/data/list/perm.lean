/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: data.list.perm
Author: Leonardo de Moura

List permutations
-/
import data.list.basic
open list setoid nat

variables {A B : Type}

inductive perm : list A → list A → Prop :=
| nil   : perm [] []
| skip  : Π (x : A) {l₁ l₂ : list A}, perm l₁ l₂ → perm (x::l₁) (x::l₂)
| swap  : Π (x y : A) (l : list A), perm (y::x::l) (x::y::l)
| trans : Π {l₁ l₂ l₃ : list A}, perm l₁ l₂ → perm l₂ l₃ → perm l₁ l₃

namespace perm
infix ~:50 := perm
theorem eq_nil_of_perm_nil {l₁ : list A} (p : [] ~ l₁) : l₁ = [] :=
have gen : ∀ (l₂ : list A) (p : l₂ ~ l₁), l₂ = [] → l₁ = [], from
  take l₂ p, perm.induction_on p
    (λ h, h)
    (λ x y l₁ l₂ p₁ r₁, list.no_confusion r₁)
    (λ x y l e, list.no_confusion e)
    (λ l₁ l₂ l₃ p₁ p₂ r₁ r₂ e, r₂ (r₁ e)),
gen [] p rfl

theorem not_perm_nil_cons (x : A) (l : list A) : ¬ [] ~ (x::l) :=
have gen : ∀ (l₁ l₂ : list A) (p : l₁ ~ l₂), l₁ = [] → l₂ = (x::l) → false, from
  take l₁ l₂ p, perm.induction_on p
    (λ e₁ e₂, list.no_confusion e₂)
    (λ x l₁ l₂ p₁ r₁ e₁ e₂, list.no_confusion e₁)
    (λ x y l e₁ e₂, list.no_confusion e₁)
    (λ l₁ l₂ l₃ p₁ p₂ r₁ r₂ e₁ e₂,
      begin
        rewrite [e₂ at *, e₁ at *],
        have e₃ : l₂ = [], from eq_nil_of_perm_nil p₁,
        exact (r₂ e₃ rfl)
      end),
assume p, gen [] (x::l) p rfl rfl

protected theorem refl : ∀ (l : list A), l ~ l
| []      := nil
| (x::xs) := skip x (refl xs)

protected theorem symm : ∀ {l₁ l₂ : list A}, l₁ ~ l₂ → l₂ ~ l₁ :=
take l₁ l₂ p, perm.induction_on p
  nil
  (λ x l₁ l₂ p₁ r₁, skip x r₁)
  (λ x y l, swap y x l)
  (λ l₁ l₂ l₃ p₁ p₂ r₁ r₂, trans r₂ r₁)

theorem eqv (A : Type) : equivalence (@perm A) :=
mk_equivalence (@perm A) (@perm.refl A) (@perm.symm A) (@perm.trans A)

protected definition is_setoid [instance] (A : Type) : setoid (list A) :=
setoid.mk (@perm A) (perm.eqv A)

calc_refl  perm.refl
calc_symm  perm.symm
calc_trans perm.trans

theorem mem_perm {a : A} {l₁ l₂ : list A} : l₁ ~ l₂ → a ∈ l₁ → a ∈ l₂ :=
assume p, perm.induction_on p
  (λ h, h)
  (λ x l₁ l₂ p₁ r₁ i, or.elim i
    (assume aeqx : a = x,   by rewrite aeqx; apply !mem_cons)
    (assume ainl₁ : a ∈ l₁, or.inr (r₁ ainl₁)))
  (λ x y l ainyxl, or.elim ainyxl
    (assume aeqy  : a = y, by rewrite aeqy; exact (or.inr !mem_cons))
    (assume ainxl : a ∈ x::l, or.elim ainxl
      (assume aeqx : a = x, or.inl aeqx)
      (assume ainl : a ∈ l, or.inr (or.inr ainl))))
  (λ l₁ l₂ l₃ p₁ p₂ r₁ r₂ ainl₁, r₂ (r₁ ainl₁))

theorem perm_app_left {l₁ l₂ : list A} (t₁ : list A) : l₁ ~ l₂ → (l₁++t₁) ~ (l₂++t₁) :=
assume p, perm.induction_on p
  !refl
  (λ x l₁ l₂ p₁ r₁, skip x r₁)
  (λ x y l, !swap)
  (λ l₁ l₂ l₃ p₁ p₂ r₁ r₂, trans r₁ r₂)

theorem perm_app_right (l : list A) {t₁ t₂ : list A} : t₁ ~ t₂ → (l++t₁) ~ (l++t₂) :=
list.induction_on l
  (λ p, p)
  (λ x xs r p, skip x (r p))

theorem perm_app {l₁ l₂ t₁ t₂ : list A} : l₁ ~ l₂ → t₁ ~ t₂ → (l₁++t₁) ~ (l₂++t₂) :=
assume p₁ p₂, trans (perm_app_left t₁ p₁) (perm_app_right l₂ p₂)

theorem perm_app_cons (a : A) {h₁ h₂ t₁ t₂ : list A} : h₁ ~ h₂ → t₁ ~ t₂ → (h₁ ++ (a::t₁)) ~ (h₂ ++ (a::t₂)) :=
assume p₁ p₂, perm_app p₁ (skip a p₂)

theorem perm_cons_app (a : A) : ∀ (l : list A), (a::l) ~ (l ++ [a])
| []      := !refl
| (x::xs) := calc
  a::x::xs ~ x::a::xs     : swap x a xs
       ... ~ x::(xs++[a]) : skip x (perm_cons_app xs)

theorem perm_app_comm {l₁ l₂ : list A} : (l₁++l₂) ~ (l₂++l₁) :=
list.induction_on l₁
  (by rewrite [append_nil_right, append_nil_left]; apply refl)
  (λ a t r, calc
    a::(t++l₂) ~ a::(l₂++t)   : skip a r
          ...  ~ l₂++t++[a]   : perm_cons_app
          ...  = l₂++(t++[a]) : append.assoc
          ...  ~ l₂++(a::t)   : perm_app_right l₂ (symm (perm_cons_app a t)))

theorem length_eq_length_of_perm {l₁ l₂ : list A} : l₁ ~ l₂ → length l₁ = length l₂ :=
assume p, perm.induction_on p
  rfl
  (λ x l₁ l₂ p r, by rewrite [*length_cons, r])
  (λ x y l, by rewrite *length_cons)
  (λ l₁ l₂ l₃ p₁ p₂ r₁ r₂, eq.trans r₁ r₂)

theorem eq_singlenton_of_perm_inv (a : A) {l : list A} : [a] ~ l → l = [a] :=
have gen : ∀ l₂, perm l₂ l → l₂ = [a] → l = [a], from
  take l₂, assume p, perm.induction_on p
    (λ e, e)
    (λ x l₁ l₂ p r e, list.no_confusion e (λ (e₁ : x = a) (e₂ : l₁ = []),
      begin
        rewrite [e₁, e₂ at p],
        have h₁ : l₂ = [], from eq_nil_of_perm_nil p,
        rewrite h₁
      end))
    (λ x y l e, list.no_confusion e (λ e₁ e₂, list.no_confusion e₂))
    (λ l₁ l₂ l₃ p₁ p₂ r₁ r₂ e, r₂ (r₁ e)),
assume p, gen [a] p rfl

theorem eq_singlenton_of_perm (a b : A) : [a] ~ [b] → a = b :=
assume p, list.no_confusion (eq_singlenton_of_perm_inv a p) (λ e₁ e₂, by rewrite e₁)

theorem perm_rev : ∀ (l : list A), l ~ (reverse l)
| []      := nil
| (x::xs) := calc
  x::xs ~ xs++[x]           : perm_cons_app x xs
    ... ~ reverse xs ++ [x] : perm_app_left [x] (perm_rev xs)
    ... = reverse (x::xs)   : by rewrite [reverse_cons, concat_eq_append]

theorem perm_middle (a : A) (l₁ l₂ : list A) : (a::l₁)++l₂ ~ l₁++(a::l₂) :=
calc
  (a::l₁) ++ l₂ = a::(l₁++l₂)   : rfl
           ...  ~ l₁++l₂++[a]   : perm_cons_app
           ...  = l₁++(l₂++[a]) : append.assoc
           ...  ~ l₁++(a::l₂)   : perm_app_right l₁ (symm (perm_cons_app a l₂))

theorem perm_cons_app_cons {l l₁ l₂ : list A} (a : A) : l ~ l₁++l₂ → a::l ~ l₁++(a::l₂) :=
assume p, calc
  a::l ~ l++[a]        : perm_cons_app
   ... ~ l₁++l₂++[a]   : perm_app_left [a] p
   ... = l₁++(l₂++[a]) : append.assoc
   ... ~ l₁++(a::l₂)   : perm_app_right l₁ (symm (perm_cons_app a l₂))

open decidable
theorem perm_erase [H : decidable_eq A] {a : A} : ∀ {l : list A}, a ∈ l → l ~ a::(erase a l)
| []     h := absurd h !not_mem_nil
| (x::t) h :=
  by_cases
    (assume aeqx  : a = x, by rewrite [aeqx, erase_cons_head]; exact !perm.refl)
    (assume naeqx : a ≠ x,
      have aint : a ∈ t,             from mem_of_ne_of_mem naeqx h,
      have aux : t ~ a :: erase a t, from perm_erase aint,
      calc x::t ~ x::a::(erase a t)   : skip x aux
            ... ~ a::x::(erase a t)   : swap
            ... = a::(erase a (x::t)) : by rewrite [!erase_cons_tail naeqx])

theorem erase_perm_erase_of_perm [H : decidable_eq A] (a : A) {l₁ l₂ : list A} : l₁ ~ l₂ → erase a l₁ ~ erase a l₂ :=
assume p, perm.induction_on p
  nil
  (λ x t₁ t₂ p r,
    by_cases
      (assume aeqx  : a = x, by rewrite [aeqx, *erase_cons_head]; exact p)
      (assume naeqx : a ≠ x, by rewrite [*erase_cons_tail _ naeqx]; exact (skip x r)))
  (λ x y l,
    by_cases
      (assume aeqx : a = x,
        by_cases
          (assume aeqy  : a = y, by rewrite [-aeqx, -aeqy]; exact !perm.refl)
          (assume naeqy : a ≠ y, by rewrite [-aeqx, erase_cons_tail _ naeqy, *erase_cons_head]; exact !perm.refl))
      (assume naeqx : a ≠ x,
        by_cases
          (assume aeqy  : a = y, by rewrite [-aeqy, erase_cons_tail _ naeqx, *erase_cons_head]; exact !perm.refl)
          (assume naeqy : a ≠ y, by rewrite[erase_cons_tail _ naeqx, *erase_cons_tail _ naeqy, erase_cons_tail _ naeqx];
                                    exact !swap)))
  (λ l₁ l₂ l₃ p₁ p₂ r₁ r₂, trans r₁ r₂)

theorem perm_induction_on {P : list A → list A → Prop} {l₁ l₂ : list A} (p : l₁ ~ l₂)
   (h₁ : P [] [])
   (h₂ : ∀ x l₁ l₂, l₁ ~ l₂ → P l₁ l₂ → P (x::l₁) (x::l₂))
   (h₃ : ∀ x y l₁ l₂, l₁ ~ l₂ → P l₁ l₂ → P (y::x::l₁) (x::y::l₂))
   (h₄ : ∀ l₁ l₂ l₃, l₁ ~ l₂ → l₂ ~ l₃ → P l₁ l₂ → P l₂ l₃ → P l₁ l₃)
   : P l₁ l₂ :=
have P_refl : ∀ l, P l l
  | []      := h₁
  | (x::xs) := h₂ x xs xs !refl (P_refl xs),
perm.induction_on p h₁ h₂ (λ x y l, h₃ x y l l !refl !P_refl) h₄

theorem xswap {l₁ l₂ : list A} (x y : A) : l₁ ~ l₂ → x::y::l₁ ~ y::x::l₂ :=
assume p, calc
  x::y::l₁  ~  y::x::l₁  : swap
        ... ~  y::x::l₂  : skip y (skip x p)

theorem perm_map (f : A → B) {l₁ l₂ : list A} : l₁ ~ l₂ → map f l₁ ~ map f l₂ :=
assume p, perm_induction_on p
  nil
  (λ x l₁ l₂ p r, skip (f x) r)
  (λ x y l₁ l₂ p r, xswap (f y) (f x) r)
  (λ l₁ l₂ l₃ p₁ p₂ r₁ r₂, trans r₁ r₂)

lemma perm_of_qeq {a : A} {l₁ l₂ : list A} : l₁≈a|l₂ → l₁~a::l₂ :=
assume q, qeq.induction_on q
  (λ h, !refl)
  (λ b t₁ t₂ q₁ r₁, calc
     b::t₂ ~ b::a::t₁ : skip b r₁
       ... ~ a::b::t₁ : swap)

/- permutation is decidable if A has decidable equality -/
section dec
open decidable
variable [Ha : decidable_eq A]
include Ha

definition decidable_perm_aux : ∀ (n : nat) (l₁ l₂ : list A), length l₁ = n → length l₂ = n → decidable (l₁ ~ l₂)
| 0     l₁      l₂ H₁ H₂ :=
  assert l₁n : l₁ = [], from eq_nil_of_length_eq_zero H₁,
  assert l₂n : l₂ = [], from eq_nil_of_length_eq_zero H₂,
  by rewrite [l₁n, l₂n]; exact (inl perm.nil)
| (n+1) (x::t₁) l₂ H₁ H₂ :=
  by_cases
    (assume xinl₂ : x ∈ l₂,
      let t₂ : list A := erase x l₂ in
      have len_t₁       : length t₁ = n,                from nat.no_confusion H₁ (λ e, e),
      assert len_t₂_aux : length t₂ = pred (length l₂), from length_erase_of_mem x l₂ xinl₂,
      assert len_t₂     : length t₂ = n,                by rewrite [len_t₂_aux, H₂],
      match decidable_perm_aux n t₁ t₂ len_t₁ len_t₂ with
      | inl p  := inl (calc
          x::t₁ ~ x::(erase x l₂) : skip x p
           ...  ~ l₂              : perm_erase xinl₂)
      | inr np := inr (λ p : x::t₁ ~ l₂,
        assert p₁ : erase x (x::t₁) ~ erase x l₂, from erase_perm_erase_of_perm x p,
        have p₂ : t₁ ~ erase x l₂, by rewrite [erase_cons_head at p₁]; exact p₁,
        absurd p₂ np)
      end)
    (assume nxinl₂ : x ∉ l₂,
      inr (λ p : x::t₁ ~ l₂, absurd (mem_perm p !mem_cons) nxinl₂))

definition decidable_perm [instance] : ∀ (l₁ l₂ : list A), decidable (l₁ ~ l₂) :=
λ l₁ l₂,
by_cases
  (assume eql : length l₁ = length l₂,
    decidable_perm_aux (length l₂) l₁ l₂ eql rfl)
  (assume neql : length l₁ ≠ length l₂,
    inr (λ p : l₁ ~ l₂, absurd (length_eq_length_of_perm p) neql))
end dec

/- permutation inversion -/
theorem perm_inv_core {l₁ l₂ : list A} (p' : l₁ ~ l₂) : ∀ {a s₁ s₂}, l₁≈a|s₁ → l₂≈a|s₂ → s₁ ~ s₂ :=
perm_induction_on p'
  (λ a s₁ s₂ e₁ e₂,
    have innil : a ∈ [], from mem_head_of_qeq e₁,
    absurd innil !not_mem_nil)
  (λ x t₁ t₂ p (r : ∀{a s₁ s₂}, t₁≈a|s₁ → t₂≈a|s₂ → s₁ ~ s₂) a s₁ s₂ e₁ e₂,
    obtain (s₁₁ s₁₂ : list A) (C₁ : s₁ = s₁₁ ++ s₁₂ ∧ x::t₁ = s₁₁++(a::s₁₂)), from qeq_split e₁,
    obtain (s₂₁ s₂₂ : list A) (C₂ : s₂ = s₂₁ ++ s₂₂ ∧ x::t₂ = s₂₁++(a::s₂₂)), from qeq_split e₂,
    begin
      cases s₁₁ with [hs₁₁, ts₁₁],
      { rewrite *append_nil_left at C₁,
        apply (list.no_confusion (and.elim_right C₁)), intros [x_eq_a, t₁_eq_s₁₂],
        rewrite [t₁_eq_s₁₂ at p, -and.elim_left C₁ at p],
        cases s₂₁ with [hs₁₂, ts₁₂],
        { rewrite *append_nil_left at C₂,
          apply (list.no_confusion (and.elim_right C₂)), intros [x_eq_a', t₂_eq_s₂₂],
          rewrite [t₂_eq_s₂₂ at p, -and.elim_left C₂ at p],
          exact p},
        { rewrite *append_cons at C₂,
          apply (list.no_confusion (and.elim_right C₂)), intros [x_eq_hs₁₂, t₂_eq_ts₁₂_a_s₂₂],
          have eq₁ : s₂ = a :: ts₁₂ ++ s₂₂, begin rewrite [-x_eq_hs₁₂ at C₂, x_eq_a at C₂]; exact (and.elim_left C₂) end,
          have p₁  : s₁ ~ ts₁₂ ++ (a :: s₂₂), begin rewrite [t₂_eq_ts₁₂_a_s₂₂ at p]; exact p end,
          have p₂  : a :: ts₁₂ ++ s₂₂ ~ ts₁₂ ++ (a :: s₂₂), from !perm_middle,
          rewrite eq₁, exact (trans p₁ (symm p₂))}},
      { rewrite *append_cons at C₁,
        apply (list.no_confusion (and.elim_right C₁)), intros [x_eq_hs₁₁, t₁_eq_ts₁₁_a_s₁₂],
        rewrite [t₁_eq_ts₁₁_a_s₁₂ at p],
        cases s₂₁ with [hs₂₁, ts₂₁],
        { rewrite *append_nil_left at C₂,
          apply (list.no_confusion (and.elim_right C₂)), intros [x_eq_a, t₂_eq_s₂₂],
          rewrite [t₂_eq_s₂₂ at p, -and.elim_left C₂ at p],
          have eq₁ : s₁ = a :: ts₁₁ ++ s₁₂,   begin rewrite [-x_eq_hs₁₁ at C₁, x_eq_a at C₁], exact (and.elim_left C₁) end,
          have p₁  : ts₁₁ ++ (a :: s₁₂) ~ s₂, from p,
          have p₂  : a :: ts₁₁ ++ s₁₂ ~ ts₁₁ ++ (a :: s₁₂), from !perm_middle,
          rewrite eq₁, exact (trans p₂ p₁)},
        { rewrite *append_cons at C₂,
          apply (list.no_confusion (and.elim_right C₂)), intros [x_eq_hs₂₁, t₂_eq_ts₂₁_a_s₂₂],
          have t₁qeq : t₁ ≈ a | (ts₁₁ ++ s₁₂), begin rewrite t₁_eq_ts₁₁_a_s₁₂, exact !qeq_app end,
          have t₂qeq : t₂ ≈ a | (ts₂₁ ++ s₂₂), begin rewrite t₂_eq_ts₂₁_a_s₂₂, exact !qeq_app end,
          have p₁ : x::(ts₁₁++s₁₂) ~ x::(ts₂₁++s₂₂), from skip x (r t₁qeq t₂qeq),
          rewrite [and.elim_left C₁, and.elim_left C₂, -x_eq_hs₁₁, -x_eq_hs₂₁],
          exact p₁}}
    end)
  (λ x y t₁ t₂ p (r : ∀{a s₁ s₂}, t₁≈a|s₁ → t₂≈a|s₂ → s₁ ~ s₂) a s₁ s₂ e₁ e₂,
    obtain (s₁₁ s₁₂ : list A) (C₁ : s₁ = s₁₁ ++ s₁₂ ∧ y::x::t₁ = s₁₁++(a::s₁₂)), from qeq_split e₁,
    obtain (s₂₁ s₂₂ : list A) (C₂ : s₂ = s₂₁ ++ s₂₂ ∧ x::y::t₂ = s₂₁++(a::s₂₂)), from qeq_split e₂,
    begin
      clears [e₁, e₂, p', l₁, l₂],
      cases s₁₁ with [hs₁₁, ts₁₁],
      { rewrite *append_nil_left at C₁,
        apply (list.no_confusion (and.elim_right C₁)), intros [y_eq_a, hs₁₂_t₁_eq_s₁₂],
        rewrite [y_eq_a at *], clear y_eq_a,
        cases s₂₁ with [hs₂₁, ts₂₁],
        { rewrite *append_nil_left at C₂,
          apply (list.no_confusion (and.elim_right C₂)), intros [x_eq_a, t₂_eq_s₂₂],
          rewrite [x_eq_a at *], clear x_eq_a,
          rewrite [and.elim_left C₁, and.elim_left C₂, -hs₁₂_t₁_eq_s₁₂, -t₂_eq_s₂₂],
          exact (skip a p)},
        { rewrite *append_cons at C₂,
          apply (list.no_confusion (and.elim_right C₂)), intros [x_eq_hs₂₁, h_t₂_eq_ts₂₁_a_s₂₂],
          rewrite x_eq_hs₂₁ at *, clear x_eq_hs₂₁,
          rewrite [and.elim_left C₁, and.elim_left C₂, -hs₁₂_t₁_eq_s₁₂],
          cases ts₂₁ with [hts₂₁, tts₂₁],
          { rewrite *append_nil_left at *,
            have t₂_eq_s₂₂ : t₂ = s₂₂, from list.no_confusion h_t₂_eq_ts₂₁_a_s₂₂ (λ h t, t),
            rewrite -t₂_eq_s₂₂,
            exact (skip _ p)},
          { rewrite append_cons at *,
            apply (list.no_confusion h_t₂_eq_ts₂₁_a_s₂₂), intros [a_eq_hts₂₁, t₂_eq_tts₂₁_a_s₂₂],
            rewrite [a_eq_hts₂₁ at t₂_eq_tts₂₁_a_s₂₂, t₂_eq_tts₂₁_a_s₂₂ at p],
            have p₁ : t₁ ~ tts₂₁ ++ (hts₂₁ :: s₂₂), from p,
            have p₂ : tts₂₁ ++ (hts₂₁ :: s₂₂) ~ hts₂₁::(tts₂₁++s₂₂), from symm (!perm_middle),
            exact (skip _ (trans p₁ p₂))}}},
      { rewrite *append_cons at *,
        apply (list.no_confusion (and.elim_right C₁)), intros [y_eq_hs₁₁, xt₁_eq_ts₁₁_a_s₁₂],
        rewrite [-y_eq_hs₁₁ at C₁], clears [y_eq_hs₁₁, hs₁₁],
        cases s₂₁ with [hs₂₁, ts₂₁],
        { rewrite *append_nil_left at C₂,
          apply (list.no_confusion (and.elim_right C₂)), intros [x_eq_a, y_t₂_eq_s₂₂],
          rewrite [-x_eq_a at (C₁, C₂, xt₁_eq_ts₁₁_a_s₁₂)], clears [x_eq_a, a],
          cases ts₁₁ with [hts₁₁, tts₁₁],
          { rewrite *append_nil_left at *,
            apply (list.no_confusion xt₁_eq_ts₁₁_a_s₁₂), intros [xeqx, t₁_eq_s₁₂], clears [xeqx, xt₁_eq_ts₁₁_a_s₁₂],
            rewrite [t₁_eq_s₁₂ at p, and.elim_left C₂, -y_t₂_eq_s₂₂, and.elim_left C₁],
            exact (skip _ p)},
          { rewrite *append_cons at *,
            apply (list.no_confusion xt₁_eq_ts₁₁_a_s₁₂), intros [x_eq_hts₁₁, t₁_eq_tts₁₁_x_s₁₂], clear xt₁_eq_ts₁₁_a_s₁₂,
            rewrite [-x_eq_hts₁₁ at C₁], clears [x_eq_hts₁₁, hts₁₁],
            cases s₂₂ with [hs₂₂, ts₂₂],
            { apply (list.no_confusion y_t₂_eq_s₂₂) },
            { apply (list.no_confusion y_t₂_eq_s₂₂), intros [y_eq_hs₂₂, t₂_eq_ts₂₂], clear y_t₂_eq_s₂₂,
              rewrite [-y_eq_hs₂₂ at C₂, -t₂_eq_ts₂₂ at C₂, t₁_eq_tts₁₁_x_s₁₂ at p],
              clears [y_eq_hs₂₂, t₂_eq_ts₂₂, t₁_eq_tts₁₁_x_s₁₂],
              have p₁ : x :: tts₁₁ ++ s₁₂ ~ t₂, from trans (!perm_middle) p,
              rewrite [and.elim_left C₁, and.elim_left C₂],
              exact (skip _ p₁)}}},
        { rewrite *append_cons at *,
          apply (list.no_confusion (and.elim_right C₂)), intros [x_eq_hs₂₁, y_t₂_eq_ts₂₁_a_s₂₂],
          rewrite [-x_eq_hs₂₁ at C₂], clears [x_eq_hs₂₁, hs₂₁],
          cases ts₁₁ with [hts₁₁, tts₁₁],
          { rewrite *append_nil_left at *,
            apply (list.no_confusion xt₁_eq_ts₁₁_a_s₁₂), intros [x_eq_a, t₁_at_s₁₂], clear xt₁_eq_ts₁₁_a_s₁₂,
            rewrite [-x_eq_a at (C₁, C₂, y_t₂_eq_ts₂₁_a_s₂₂), -t₁_at_s₁₂ at C₁], clears [x_eq_a, a, t₁_at_s₁₂, s₁₂],
            cases ts₂₁ with [hts₂₁, tts₂₁],
            { rewrite *append_nil_left at *,
              apply (list.no_confusion y_t₂_eq_ts₂₁_a_s₂₂), intros [y_eq_x, t₂_eq_s₂₂], clear y_t₂_eq_ts₂₁_a_s₂₂,
              rewrite [y_eq_x at (C₁, C₂), -t₂_eq_s₂₂ at (C₁, C₂)], clears [y_eq_x, t₂_eq_s₂₂],
              rewrite [and.elim_left C₁, and.elim_left C₂],
              exact (skip _ p)},
            { rewrite *append_cons at *,
              apply (list.no_confusion y_t₂_eq_ts₂₁_a_s₂₂), intros [y_eq_hts₂₁, t₂_eq_tts₂₁_x_s₂₂], clear y_t₂_eq_ts₂₁_a_s₂₂,
              rewrite [-y_eq_hts₂₁ at C₂, t₂_eq_tts₂₁_x_s₂₂ at p],
              have p₁ : y::t₁ ~ y::x::(tts₂₁ ++ s₂₂), from skip y (trans p (symm !perm_middle)),
              have p₂ : y::x::(tts₂₁ ++ s₂₂) ~ x::y::(tts₂₁ ++ s₂₂), from !swap,
              rewrite [and.elim_left C₁, and.elim_left C₂],
              exact (trans p₁ p₂)}},
          { rewrite *append_cons at *,
            apply (list.no_confusion xt₁_eq_ts₁₁_a_s₁₂), intros [x_eq_hts₁₁, t₁_eq_tts₁₁_a_s₁₂], clear xt₁_eq_ts₁₁_a_s₁₂,
            rewrite [-x_eq_hts₁₁ at C₁], clears [x_eq_hts₁₁, hts₁₁],
            cases ts₂₁ with [hts₂₁, tts₂₁],
            { rewrite *append_nil_left at *,
              apply (list.no_confusion y_t₂_eq_ts₂₁_a_s₂₂), intros [y_eq_a, t₂_eq_s₂₂], clear y_t₂_eq_ts₂₁_a_s₂₂,
              rewrite [-y_eq_a at (C₁, C₂, t₁_eq_tts₁₁_a_s₁₂), -t₂_eq_s₂₂ at C₂, t₁_eq_tts₁₁_a_s₁₂ at p],
              clears [y_eq_a, a, t₂_eq_s₂₂, s₂₂],
              have p₁ : x::y::(tts₁₁ ++ s₁₂) ~ x::t₂, from skip x (trans !perm_middle p),
              have p₂ : y::x::(tts₁₁ ++ s₁₂) ~ x::y::(tts₁₁ ++ s₁₂), from !swap,
              rewrite [and.elim_left C₁, and.elim_left C₂],
              exact (trans p₂ p₁)},
            { rewrite *append_cons at *,
              apply (list.no_confusion y_t₂_eq_ts₂₁_a_s₂₂), intros [y_eq_hts₂₁, t₂_eq_tts₂₁_a_s₂₂], clear y_t₂_eq_ts₂₁_a_s₂₂,
              rewrite [-y_eq_hts₂₁ at C₂], clears [y_eq_hts₂₁, hts₂₁],
              have aux₁ : tts₁₁ ++ (a :: s₁₂) ≈ a|(tts₁₁ ++ s₁₂), from !qeq_app,
              have aux₂ : tts₂₁ ++ (a :: s₂₂) ≈ a|(tts₂₁ ++ s₂₂), from !qeq_app,
              rewrite [-t₁_eq_tts₁₁_a_s₁₂ at aux₁, -t₂_eq_tts₂₁_a_s₂₂ at aux₂],
              have p₁ : y::x::(tts₁₁ ++ s₁₂) ~ y::x::(tts₂₁ ++ s₂₂), from skip y (skip x (r aux₁ aux₂)),
              have p₂ : y::x::(tts₂₁ ++ s₂₂) ~ x::y::(tts₂₁ ++ s₂₂), from !swap,
              rewrite [and.elim_left C₁, and.elim_left C₂],
              exact (trans p₁ p₂)}}}}
    end)
  (λ t₁ t₂ t₃ p₁ p₂
     (r₁ : ∀{a s₁ s₂}, t₁ ≈ a|s₁ → t₂≈a|s₂ → s₁ ~ s₂)
     (r₂ : ∀{a s₁ s₂}, t₂ ≈ a|s₁ → t₃≈a|s₂ → s₁ ~ s₂)
     a s₁ s₂ e₁ e₂,
    have aint₁ : a ∈ t₁, from mem_head_of_qeq e₁,
    have aint₂ : a ∈ t₂, from mem_perm p₁ aint₁,
    obtain (t₂' : list A) (e₂' : t₂≈a|t₂'), from qeq_of_mem aint₂,
    calc s₁  ~ t₂' : r₁ e₁ e₂'
        ...  ~ s₂  : r₂ e₂' e₂)

theorem perm_cons_inv {a : A} {l₁ l₂ : list A} : a::l₁ ~ a::l₂ → l₁ ~ l₂ :=
assume p, perm_inv_core p (qeq.qhead a l₁) (qeq.qhead a l₂)

theorem perm_app_inv {a : A} {l₁ l₂ l₃ l₄ : list A} : l₁++(a::l₂) ~ l₃++(a::l₄) → l₁++l₂ ~ l₃++l₄ :=
assume p : l₁++(a::l₂) ~ l₃++(a::l₄),
  have p' : a::(l₁++l₂) ~ a::(l₃++l₄), from calc
    a::(l₁++l₂) ~ l₁++(a::l₂) : perm_middle
          ...   ~ l₃++(a::l₄) : p
          ...   ~ a::(l₃++l₄) : symm (!perm_middle),
  perm_cons_inv p'
end perm
