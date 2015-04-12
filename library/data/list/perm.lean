/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: data.list.perm
Author: Leonardo de Moura

List permutations
-/
import data.list.basic data.list.set
open list setoid nat binary

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
  (λ x l₁ l₂ p₁ r₁ i, or.elim (eq_or_mem_of_mem_cons i)
    (assume aeqx : a = x,   by rewrite aeqx; apply !mem_cons)
    (assume ainl₁ : a ∈ l₁, or.inr (r₁ ainl₁)))
  (λ x y l ainyxl, or.elim (eq_or_mem_of_mem_cons ainyxl)
    (assume aeqy  : a = y, by rewrite aeqy; exact (or.inr !mem_cons))
    (assume ainxl : a ∈ x::l, or.elim (eq_or_mem_of_mem_cons ainxl)
      (assume aeqx : a = x, or.inl aeqx)
      (assume ainl : a ∈ l, or.inr (or.inr ainl))))
  (λ l₁ l₂ l₃ p₁ p₂ r₁ r₂ ainl₁, r₂ (r₁ ainl₁))

theorem not_mem_perm {a : A} {l₁ l₂ : list A} : l₁ ~ l₂ → a ∉ l₁ → a ∉ l₂ :=
assume p nainl₁ ainl₂, absurd (mem_perm (symm p) ainl₂) nainl₁

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
      assert len_t₂_aux : length t₂ = pred (length l₂), from length_erase_of_mem xinl₂,
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

-- Auxiliary theorem for performing cases-analysis on l₂.
-- We use it to prove perm_inv_core.
private theorem discr {P : Prop} {a b : A} {l₁ l₂ l₃ : list A} :
    a::l₁ = l₂++(b::l₃)                    →
    (l₂ = [] → a = b → l₁ = l₃ → P)        →
    (∀ t, l₂ = a::t → l₁ = t++(b::l₃) → P) → P :=
match l₂ with
| []   := λ e h₁ h₂, list.no_confusion e (λ e₁ e₂, h₁ rfl e₁ e₂)
| h::t := λ e h₁ h₂,
  begin
    apply (list.no_confusion e), intros [e₁, e₂],
    rewrite e₁ at h₂,
    exact (h₂ t rfl e₂)
  end
end

-- Auxiliary theorem for performing cases-analysis on l₂.
-- We use it to prove perm_inv_core.
private theorem discr₂ {P : Prop} {a b c : A} {l₁ l₂ l₃ : list A} :
    a::b::l₁ = l₂++(c::l₃)                     →
    (l₂ = [] → l₃ = b::l₁ → a = c → P)         →
    (l₂ = [a] → b = c → l₁ = l₃ → P)           →
    (∀ t, l₂ = a::b::t → l₁ = t++(c::l₃) → P)  → P :=
match l₂ with
| []   := λ e H₁ H₂ H₃,
   list.no_confusion e (λ a_eq_c b_l₁_eq_l₃, H₁ rfl (eq.symm b_l₁_eq_l₃) a_eq_c)
| [h₁] := λ e H₁ H₂ H₃,
  begin
    rewrite [append_cons at e, append_nil_left at e],
    apply (list.no_confusion e), intros [a_eq_h₁, rest],
    apply (list.no_confusion rest), intros [b_eq_c, l₁_eq_l₃],
    rewrite [a_eq_h₁ at H₂, b_eq_c at H₂, l₁_eq_l₃ at H₂],
    exact (H₂ rfl rfl rfl)
  end
| h₁::h₂::t₂ := λ e H₁ H₂ H₃,
  begin
    apply (list.no_confusion e),    intros [a_eq_h₁, rest],
    apply (list.no_confusion rest), intros [b_eq_h₂, l₁_eq],
    rewrite [a_eq_h₁ at H₃, b_eq_h₂ at H₃],
    exact (H₃ t₂ rfl l₁_eq)
  end
end

/- permutation inversion -/
theorem perm_inv_core {l₁ l₂ : list A} (p' : l₁ ~ l₂) : ∀ {a s₁ s₂}, l₁≈a|s₁ → l₂≈a|s₂ → s₁ ~ s₂ :=
perm_induction_on p'
  (λ a s₁ s₂ e₁ e₂,
    have innil : a ∈ [], from mem_head_of_qeq e₁,
    absurd innil !not_mem_nil)
  (λ x t₁ t₂ p (r : ∀{a s₁ s₂}, t₁≈a|s₁ → t₂≈a|s₂ → s₁ ~ s₂) a s₁ s₂ e₁ e₂,
    obtain (s₁₁ s₁₂ : list A) (C₁ : s₁ = s₁₁ ++ s₁₂ ∧ x::t₁ = s₁₁++(a::s₁₂)), from qeq_split e₁,
    obtain (s₂₁ s₂₂ : list A) (C₂ : s₂ = s₂₁ ++ s₂₂ ∧ x::t₂ = s₂₁++(a::s₂₂)), from qeq_split e₂,
    discr (and.elim_right C₁)
      (λ (s₁₁_eq : s₁₁ = []) (x_eq_a : x = a) (t₁_eq : t₁ = s₁₂),
        assert s₁_p : s₁ ~ t₂, from calc
            s₁  = s₁₁ ++ s₁₂ : and.elim_left C₁
            ... = t₁         : by rewrite [-t₁_eq, s₁₁_eq, append_nil_left]
            ... ~ t₂         : p,
        discr (and.elim_right C₂)
          (λ (s₂₁_eq : s₂₁ = []) (x_eq_a : x = a) (t₂_eq: t₂ = s₂₂),
            proof calc
              s₁  ~ t₂         : s₁_p
              ... = s₂₁ ++ s₂₂ : by rewrite [-t₂_eq, s₂₁_eq, append_nil_left]
              ... = s₂         : by rewrite [and.elim_left C₂]
            qed)
          (λ (ts₂₁ : list A) (s₂₁_eq : s₂₁ = x::ts₂₁) (t₂_eq : t₂ = ts₂₁++(a::s₂₂)),
            proof calc
              s₁  ~ t₂             : s₁_p
              ... = ts₂₁++(a::s₂₂) : t₂_eq
              ... ~ (a::ts₂₁)++s₂₂ : !perm_middle
              ... = s₂₁ ++ s₂₂     : by rewrite [-x_eq_a, -s₂₁_eq]
              ... = s₂             : by rewrite [and.elim_left C₂]
            qed))
      (λ (ts₁₁ : list A) (s₁₁_eq : s₁₁ = x::ts₁₁) (t₁_eq : t₁ = ts₁₁++(a::s₁₂)),
        assert t₁_qeq : t₁ ≈ a|(ts₁₁++s₁₂), by rewrite t₁_eq; exact !qeq_app,
        assert s₁_eq : s₁ = x::(ts₁₁++s₁₂), from calc
          s₁  = s₁₁ ++ s₁₂       : and.elim_left C₁
          ... = x::(ts₁₁++ s₁₂)  : by rewrite s₁₁_eq,
        discr (and.elim_right C₂)
          (λ (s₂₁_eq : s₂₁ = []) (x_eq_a : x = a) (t₂_eq: t₂ = s₂₂),
            proof calc
              s₁  = a::(ts₁₁++s₁₂) : by rewrite [s₁_eq, x_eq_a]
              ... ~ ts₁₁++(a::s₁₂) : !perm_middle
              ... = t₁             : t₁_eq
              ... ~ t₂             : p
              ... = s₂             : by rewrite [t₂_eq, and.elim_left C₂, s₂₁_eq, append_nil_left]
            qed)
          (λ (ts₂₁ : list A) (s₂₁_eq : s₂₁ = x::ts₂₁) (t₂_eq : t₂ = ts₂₁++(a::s₂₂)),
            assert t₂_qeq : t₂ ≈ a|(ts₂₁++s₂₂), by rewrite t₂_eq; exact !qeq_app,
            proof calc
              s₁  = x::(ts₁₁++s₁₂) : s₁_eq
              ... ~ x::(ts₂₁++s₂₂) : skip x (r t₁_qeq t₂_qeq)
              ... = s₂             : by rewrite [-append_cons, -s₂₁_eq, and.elim_left C₂]
            qed)))
  (λ x y t₁ t₂ p (r : ∀{a s₁ s₂}, t₁≈a|s₁ → t₂≈a|s₂ → s₁ ~ s₂) a s₁ s₂ e₁ e₂,
    obtain (s₁₁ s₁₂ : list A) (C₁ : s₁ = s₁₁ ++ s₁₂ ∧ y::x::t₁ = s₁₁++(a::s₁₂)), from qeq_split e₁,
    obtain (s₂₁ s₂₂ : list A) (C₂ : s₂ = s₂₁ ++ s₂₂ ∧ x::y::t₂ = s₂₁++(a::s₂₂)), from qeq_split e₂,
    discr₂ (and.elim_right C₁)
      (λ (s₁₁_eq : s₁₁ = [])  (s₁₂_eq : s₁₂ = x::t₁) (y_eq_a : y = a),
        assert s₁_p : s₁ ~ x::t₂, from calc
            s₁  = s₁₁ ++ s₁₂ : and.elim_left C₁
            ... = x::t₁      : by rewrite [s₁₂_eq, s₁₁_eq, append_nil_left]
            ... ~ x::t₂      : skip x p,
        discr₂ (and.elim_right C₂)
          (λ (s₂₁_eq : s₂₁ = [])  (s₂₂_eq : s₂₂ = y::t₂) (x_eq_a : x = a),
            proof calc
              s₁  ~ x::t₂      : s₁_p
              ... = s₂₁ ++ s₂₂ : by rewrite [x_eq_a, -y_eq_a, -s₂₂_eq, s₂₁_eq, append_nil_left]
              ... = s₂         : by rewrite [and.elim_left C₂]
            qed)
          (λ (s₂₁_eq : s₂₁ = [x]) (y_eq_a : y = a) (t₂_eq : t₂ = s₂₂),
            proof calc
              s₁  ~ x::t₂      : s₁_p
              ... = s₂₁ ++ s₂₂ : by rewrite [t₂_eq, s₂₁_eq, append_cons]
              ... = s₂         : by rewrite [and.elim_left C₂]
            qed)
          (λ (ts₂₁ : list A) (s₂₁_eq : s₂₁ = x::y::ts₂₁) (t₂_eq : t₂ = ts₂₁++(a::s₂₂)),
            proof calc
              s₁  ~ x::t₂               : s₁_p
              ... = x::(ts₂₁++(y::s₂₂)) : by rewrite [t₂_eq, -y_eq_a]
              ... ~ x::y::(ts₂₁++s₂₂)   : skip x !perm_middle
              ... = s₂₁ ++ s₂₂          : by rewrite [s₂₁_eq, append_cons]
              ... = s₂                  : by rewrite [and.elim_left C₂]
            qed))
      (λ (s₁₁_eq : s₁₁ = [y]) (x_eq_a : x = a) (t₁_eq : t₁ = s₁₂),
        assert s₁_p : s₁ ~ y::t₂, from calc
             s₁  = y::t₁ : by rewrite [and.elim_left C₁, s₁₁_eq, t₁_eq]
             ... ~ y::t₂ : skip y p,
        discr₂ (and.elim_right C₂)
          (λ (s₂₁_eq : s₂₁ = [])  (s₂₂_eq : s₂₂ = y::t₂) (x_eq_a : x = a),
            proof calc
              s₁  ~ y::t₂      : s₁_p
              ... = s₂₁ ++ s₂₂ : by rewrite [s₂₁_eq, s₂₂_eq]
              ... = s₂         : by rewrite [and.elim_left C₂]
            qed)
          (λ (s₂₁_eq : s₂₁ = [x]) (y_eq_a : y = a) (t₂_eq : t₂ = s₂₂),
            proof calc
              s₁  ~ y::t₂      : s₁_p
              ... = s₂₁ ++ s₂₂ : by rewrite [s₂₁_eq, t₂_eq, y_eq_a, -x_eq_a]
              ... = s₂         : by rewrite [and.elim_left C₂]
            qed)
          (λ (ts₂₁ : list A) (s₂₁_eq : s₂₁ = x::y::ts₂₁) (t₂_eq : t₂ = ts₂₁++(a::s₂₂)),
            proof calc
              s₁  ~ y::t₂               : s₁_p
              ... = y::(ts₂₁++(x::s₂₂)) : by rewrite [t₂_eq, -x_eq_a]
              ... ~ y::x::(ts₂₁++s₂₂)   : skip y !perm_middle
              ... ~ x::y::(ts₂₁++s₂₂)   : swap
              ... = s₂₁ ++ s₂₂          : by rewrite [s₂₁_eq]
              ... = s₂                  : by rewrite [and.elim_left C₂]
            qed))
      (λ (ts₁₁ : list A) (s₁₁_eq : s₁₁ = y::x::ts₁₁) (t₁_eq : t₁ = ts₁₁++(a::s₁₂)),
        assert s₁_eq  : s₁ = y::x::(ts₁₁++s₁₂), by rewrite [and.elim_left C₁, s₁₁_eq],
        discr₂ (and.elim_right C₂)
          (λ (s₂₁_eq : s₂₁ = [])  (s₂₂_eq : s₂₂ = y::t₂) (x_eq_a : x = a),
            proof calc
              s₁  = y::a::(ts₁₁++s₁₂)   : by rewrite [s₁_eq, x_eq_a]
              ... ~ y::(ts₁₁++(a::s₁₂)) : skip y !perm_middle
              ... = y::t₁               : by rewrite t₁_eq
              ... ~ y::t₂               : skip y p
              ... = s₂₁ ++ s₂₂          : by rewrite [s₂₁_eq, s₂₂_eq]
              ... = s₂                  : by rewrite [and.elim_left C₂]
            qed)
          (λ (s₂₁_eq : s₂₁ = [x]) (y_eq_a : y = a) (t₂_eq : t₂ = s₂₂),
            proof calc
              s₁  = y::x::(ts₁₁++s₁₂)   : by rewrite s₁_eq
              ... ~ x::y::(ts₁₁++s₁₂)   : swap
              ... = x::a::(ts₁₁++s₁₂)   : by rewrite y_eq_a
              ... ~ x::(ts₁₁++(a::s₁₂)) : skip x !perm_middle
              ... = x::t₁               : by rewrite t₁_eq
              ... ~ x::t₂               : skip x p
              ... = s₂₁ ++ s₂₂          : by rewrite [t₂_eq, s₂₁_eq]
              ... = s₂                  : by rewrite [and.elim_left C₂]
            qed)
          (λ (ts₂₁ : list A) (s₂₁_eq : s₂₁ = x::y::ts₂₁) (t₂_eq : t₂ = ts₂₁++(a::s₂₂)),
            assert t₁_qeq : t₁ ≈ a|(ts₁₁++s₁₂),    by rewrite t₁_eq; exact !qeq_app,
            assert t₂_qeq : t₂ ≈ a|(ts₂₁++s₂₂),    by rewrite t₂_eq; exact !qeq_app,
            assert p_aux  : ts₁₁++s₁₂ ~ ts₂₁++s₂₂, from r t₁_qeq t₂_qeq,
            proof calc
              s₁  = y::x::(ts₁₁++s₁₂)   : by rewrite s₁_eq
              ... ~ y::x::(ts₂₁++s₂₂)   : skip y (skip x p_aux)
              ... ~ x::y::(ts₂₁++s₂₂)   : swap
              ... = s₂₁ ++ s₂₂          : by rewrite s₂₁_eq
              ... = s₂                  : by rewrite [and.elim_left C₂]
            qed)))
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

section foldl
  variables {f : B → A → B} {l₁ l₂ : list A}
  variable rcomm : right_commutative f
  include  rcomm

  theorem foldl_eq_of_perm : l₁ ~ l₂ → ∀ b, foldl f b l₁ = foldl f b l₂ :=
  assume p, perm_induction_on p
    (λ b, by rewrite *foldl_nil)
    (λ x t₁ t₂ p r b, calc
       foldl f b (x::t₁) = foldl f (f b x) t₁ : foldl_cons
               ...       = foldl f (f b x) t₂ : r (f b x)
               ...       = foldl f b (x::t₂)  : foldl_cons)
    (λ x y t₁ t₂ p r b, calc
       foldl f b (y :: x :: t₁) = foldl f (f (f b y) x) t₁ : by rewrite foldl_cons
                     ...        = foldl f (f (f b x) y) t₁ : by rewrite rcomm
                     ...        = foldl f (f (f b x) y) t₂ : r (f (f b x) y)
                     ...        = foldl f b (x :: y :: t₂) : by rewrite foldl_cons)
    (λ t₁ t₂ t₃ p₁ p₂ r₁ r₂ b, eq.trans (r₁ b) (r₂ b))
end foldl

section foldr
  variables {f : A → B → B} {l₁ l₂ : list A}
  variable lcomm : left_commutative f
  include  lcomm

  theorem foldr_eq_of_perm : l₁ ~ l₂ → ∀ b, foldr f b l₁ = foldr f b l₂ :=
  assume p, perm_induction_on p
    (λ b, by rewrite *foldl_nil)
    (λ x t₁ t₂ p r b, calc
       foldr f b (x::t₁) = f x (foldr f b t₁) : foldr_cons
               ...       = f x (foldr f b t₂) : by rewrite [r b]
               ...       = foldr f b (x::t₂)  : foldr_cons)
    (λ x y t₁ t₂ p r b, calc
       foldr f b (y :: x :: t₁) = f y (f x (foldr f b t₁)) : by rewrite foldr_cons
                  ...           = f x (f y (foldr f b t₁)) : by rewrite lcomm
                  ...           = f x (f y (foldr f b t₂)) : by rewrite [r b]
                  ...           = foldr f b (x :: y :: t₂) : by rewrite foldr_cons)
    (λ t₁ t₂ t₃ p₁ p₂ r₁ r₂ a, eq.trans (r₁ a) (r₂ a))
end foldr

theorem perm_erase_dup_of_perm [H : decidable_eq A] {l₁ l₂ : list A} : l₁ ~ l₂ → erase_dup l₁ ~ erase_dup l₂ :=
assume p, perm_induction_on p
  nil
  (λ x t₁ t₂ p r, by_cases
    (λ xint₁  : x ∈ t₁,
      assert xint₂ : x ∈ t₂, from mem_of_mem_erase_dup (mem_perm r (mem_erase_dup xint₁)),
      by rewrite [erase_dup_cons_of_mem xint₁, erase_dup_cons_of_mem xint₂]; exact r)
    (λ nxint₁ : x ∉ t₁,
      assert nxint₂ : x ∉ t₂, from
         assume xint₂ : x ∈ t₂, absurd (mem_of_mem_erase_dup (mem_perm (symm r) (mem_erase_dup xint₂))) nxint₁,
      by rewrite [erase_dup_cons_of_not_mem nxint₂, erase_dup_cons_of_not_mem nxint₁]; exact (skip x r)))
  (λ y x t₁ t₂ p r, by_cases
    (λ xinyt₁  : x ∈ y::t₁, by_cases
      (λ yint₁  : y ∈ t₁,
        assert yint₂  : y ∈ t₂,    from mem_of_mem_erase_dup (mem_perm r (mem_erase_dup yint₁)),
        assert yinxt₂ : y ∈ x::t₂, from or.inr (yint₂),
        or.elim (eq_or_mem_of_mem_cons xinyt₁)
          (λ xeqy  : x = y,
            assert xint₂ : x ∈ t₂, by rewrite [-xeqy at yint₂]; exact yint₂,
            begin
              rewrite [erase_dup_cons_of_mem xinyt₁, erase_dup_cons_of_mem yinxt₂,
                       erase_dup_cons_of_mem yint₁, erase_dup_cons_of_mem xint₂],
              exact r
            end)
          (λ xint₁ : x ∈ t₁,
            assert xint₂ : x ∈ t₂, from mem_of_mem_erase_dup (mem_perm r (mem_erase_dup xint₁)),
            begin
              rewrite [erase_dup_cons_of_mem xinyt₁, erase_dup_cons_of_mem yinxt₂,
                       erase_dup_cons_of_mem yint₁, erase_dup_cons_of_mem xint₂],
              exact r
            end))
      (λ nyint₁ : y ∉ t₁,
        assert nyint₂ : y ∉ t₂, from
          assume yint₂ : y ∈ t₂, absurd (mem_of_mem_erase_dup (mem_perm (symm r) (mem_erase_dup yint₂))) nyint₁,
        by_cases
          (λ xeqy  : x = y,
            assert nxint₂ : x ∉ t₂, by rewrite [-xeqy at nyint₂]; exact nyint₂,
            assert yinxt₂ : y ∈ x::t₂, by rewrite [xeqy]; exact !mem_cons,
            begin
              rewrite [erase_dup_cons_of_mem xinyt₁, erase_dup_cons_of_mem yinxt₂,
                       erase_dup_cons_of_not_mem nyint₁, erase_dup_cons_of_not_mem nxint₂, xeqy],
              exact (skip y r)
            end)
          (λ xney : x ≠ y,
            have xint₁     : x ∈ t₁, from or_resolve_right xinyt₁ xney,
            assert xint₂   : x ∈ t₂, from mem_of_mem_erase_dup (mem_perm r (mem_erase_dup xint₁)),
            assert nyinxt₂ : y ∉ x::t₂, from
              assume yinxt₂ : y ∈ x::t₂, or.elim (eq_or_mem_of_mem_cons yinxt₂)
                (λ h, absurd h (ne.symm xney))
                (λ h, absurd h nyint₂),
            begin
              rewrite [erase_dup_cons_of_mem xinyt₁, erase_dup_cons_of_not_mem nyinxt₂,
                       erase_dup_cons_of_not_mem nyint₁, erase_dup_cons_of_mem xint₂],
              exact (skip y r)
            end)))
    (λ nxinyt₁ : x ∉ y::t₁,
      have   xney    : x ≠ y,  from not_eq_of_not_mem nxinyt₁,
      have   nxint₁  : x ∉ t₁, from not_mem_of_not_mem nxinyt₁,
      assert nxint₂  : x ∉ t₂, from
        assume xint₂ : x ∈ t₂, absurd (mem_of_mem_erase_dup (mem_perm (symm r) (mem_erase_dup xint₂))) nxint₁,
      by_cases
        (λ yint₁  : y ∈ t₁,
          assert yinxt₂ : y ∈ x::t₂, from or.inr (mem_of_mem_erase_dup (mem_perm r (mem_erase_dup yint₁))),
          begin
            rewrite [erase_dup_cons_of_not_mem nxinyt₁, erase_dup_cons_of_mem yinxt₂,
                     erase_dup_cons_of_mem yint₁, erase_dup_cons_of_not_mem nxint₂],
            exact (skip x r)
          end)
        (λ nyint₁ : y ∉ t₁,
          assert nyinxt₂ : y ∉ x::t₂, from
            assume yinxt₂ : y ∈ x::t₂, or.elim (eq_or_mem_of_mem_cons yinxt₂)
              (λ h, absurd h (ne.symm xney))
              (λ h, absurd (mem_of_mem_erase_dup (mem_perm (symm r) (mem_erase_dup h))) nyint₁),
          begin
            rewrite [erase_dup_cons_of_not_mem nxinyt₁, erase_dup_cons_of_not_mem nyinxt₂,
                     erase_dup_cons_of_not_mem nyint₁, erase_dup_cons_of_not_mem nxint₂],
            exact (xswap x y r)
          end)))
  (λ t₁ t₂ t₃ p₁ p₂ r₁ r₂, trans r₁ r₂)

section perm_union
variable [H : decidable_eq A]
include H

theorem perm_union_left {l₁ l₂ : list A} (t₁ : list A) : l₁ ~ l₂ → (union l₁ t₁) ~ (union l₂ t₁) :=
assume p, perm.induction_on p
  (by rewrite [nil_union]; exact !refl)
  (λ x l₁ l₂ p₁ r₁, by_cases
     (λ xint₁  : x ∈ t₁, by rewrite [*union_cons_of_mem _ xint₁]; exact r₁)
     (λ nxint₁ : x ∉ t₁, by rewrite [*union_cons_of_not_mem _ nxint₁]; exact (skip _ r₁)))
  (λ x y l, by_cases
    (λ yint  : y ∈ t₁, by_cases
      (λ xint  : x ∈ t₁,
        by rewrite [*union_cons_of_mem _ xint, *union_cons_of_mem _ yint, *union_cons_of_mem _ xint]; exact !refl)
      (λ nxint : x ∉ t₁,
        by rewrite [*union_cons_of_mem _ yint, *union_cons_of_not_mem _ nxint, union_cons_of_mem _ yint]; exact !refl))
    (λ nyint : y ∉ t₁, by_cases
      (λ xint  : x ∈ t₁,
        by rewrite [*union_cons_of_mem _ xint, *union_cons_of_not_mem _ nyint, union_cons_of_mem _ xint]; exact !refl)
      (λ nxint : x ∉ t₁,
        by rewrite [*union_cons_of_not_mem _ nxint, *union_cons_of_not_mem _ nyint, union_cons_of_not_mem _ nxint]; exact !swap)))
  (λ l₁ l₂ l₃ p₁ p₂ r₁ r₂, trans r₁ r₂)

theorem perm_union_right (l : list A) {t₁ t₂ : list A} : t₁ ~ t₂ → (union l t₁) ~ (union l t₂) :=
list.induction_on l
  (λ p, by rewrite [*union_nil]; exact p)
  (λ x xs r p, by_cases
    (λ xint₁  : x ∈ t₁,
      assert xint₂ : x ∈ t₂, from mem_perm p xint₁,
      by rewrite [union_cons_of_mem _ xint₁, union_cons_of_mem _ xint₂]; exact (r p))
    (λ nxint₁ : x ∉ t₁,
      assert nxint₂ : x ∉ t₂, from not_mem_perm p nxint₁,
      by rewrite [union_cons_of_not_mem _ nxint₁, union_cons_of_not_mem _ nxint₂]; exact (skip _ (r p))))

theorem perm_union {l₁ l₂ t₁ t₂ : list A} : l₁ ~ l₂ → t₁ ~ t₂ → (union l₁ t₁) ~ (union l₂ t₂) :=
assume p₁ p₂, trans (perm_union_left t₁ p₁) (perm_union_right l₂ p₂)
end perm_union

section perm_insert
variable [H : decidable_eq A]
include H

theorem perm_insert (a : A) {l₁ l₂ : list A} : l₁ ~ l₂ → (insert a l₁) ~ (insert a l₂) :=
assume p, by_cases
 (λ ainl₁  : a ∈ l₁,
   assert ainl₂ : a ∈ l₂, from mem_perm p ainl₁,
   by rewrite [insert_eq_of_mem ainl₁, insert_eq_of_mem ainl₂]; exact p)
 (λ nainl₁ : a ∉ l₁,
   assert nainl₂ : a ∉ l₂, from not_mem_perm p nainl₁,
   by rewrite [insert_eq_of_not_mem nainl₁, insert_eq_of_not_mem nainl₂]; exact (skip _ p))
end perm_insert

section perm_intersection
variable [H : decidable_eq A]
include H

theorem perm_intersection_left {l₁ l₂ : list A} (t₁ : list A) : l₁ ~ l₂ → (intersection l₁ t₁) ~ (intersection l₂ t₁) :=
assume p, perm.induction_on p
  !refl
  (λ x l₁ l₂ p₁ r₁, by_cases
    (λ xint₁  : x ∈ t₁, by rewrite [*intersection_cons_of_mem _ xint₁]; exact (skip x r₁))
    (λ nxint₁ : x ∉ t₁, by rewrite [*intersection_cons_of_not_mem _ nxint₁]; exact r₁))
  (λ x y l, by_cases
    (λ yint  : y ∈ t₁, by_cases
      (λ xint  : x ∈ t₁,
        by rewrite [*intersection_cons_of_mem _ xint, *intersection_cons_of_mem _ yint, *intersection_cons_of_mem _ xint];
           exact !swap)
      (λ nxint : x ∉ t₁,
        by rewrite [*intersection_cons_of_mem _ yint, *intersection_cons_of_not_mem _ nxint, intersection_cons_of_mem _ yint];
           exact !refl))
    (λ nyint : y ∉ t₁, by_cases
      (λ xint  : x ∈ t₁,
        by rewrite [*intersection_cons_of_mem _ xint, *intersection_cons_of_not_mem _ nyint, intersection_cons_of_mem _ xint];
           exact !refl)
      (λ nxint : x ∉ t₁,
        by rewrite [*intersection_cons_of_not_mem _ nxint, *intersection_cons_of_not_mem _ nyint,
                     intersection_cons_of_not_mem _ nxint];
           exact !refl)))
  (λ l₁ l₂ l₃ p₁ p₂ r₁ r₂, trans r₁ r₂)

theorem perm_intersection_right (l : list A) {t₁ t₂ : list A} : t₁ ~ t₂ → (intersection l t₁) ~ (intersection l t₂) :=
list.induction_on l
  (λ p, by rewrite [*intersection_nil]; exact !refl)
  (λ x xs r p, by_cases
    (λ xint₁  : x ∈ t₁,
      assert xint₂ : x ∈ t₂, from mem_perm p xint₁,
      by rewrite [intersection_cons_of_mem _ xint₁, intersection_cons_of_mem _ xint₂]; exact (skip _ (r p)))
    (λ nxint₁ : x ∉ t₁,
      assert nxint₂ : x ∉ t₂, from not_mem_perm p nxint₁,
      by rewrite [intersection_cons_of_not_mem _ nxint₁, intersection_cons_of_not_mem _ nxint₂]; exact (r p)))

theorem perm_intersection {l₁ l₂ t₁ t₂ : list A} : l₁ ~ l₂ → t₁ ~ t₂ → (intersection l₁ t₁) ~ (intersection l₂ t₂) :=
assume p₁ p₂, trans (perm_intersection_left t₁ p₁) (perm_intersection_right l₂ p₂)
end perm_intersection

/- extensionality -/
section ext
open eq.ops

theorem perm_ext : ∀ {l₁ l₂ : list A}, nodup l₁ → nodup l₂ → (∀a, a ∈ l₁ ↔ a ∈ l₂) → l₁ ~ l₂
| []       []       d₁ d₂ e := !perm.nil
| []       (a₂::t₂) d₁ d₂ e := absurd (iff.mp' (e a₂) !mem_cons) (not_mem_nil a₂)
| (a₁::t₁) []       d₁ d₂ e := absurd (iff.mp (e a₁) !mem_cons) (not_mem_nil a₁)
| (a₁::t₁) (a₂::t₂) d₁ d₂ e :=
  have a₁inl₂   : a₁ ∈ a₂::t₂, from iff.mp (e a₁) !mem_cons,
  have dt₁      : nodup t₁, from nodup_of_nodup_cons d₁,
  have na₁int₁  : a₁ ∉ t₁, from not_mem_of_nodup_cons d₁,
  have ex : ∃s₁ s₂, a₂::t₂ = s₁++(a₁::s₂), from mem_split a₁inl₂,
  obtain (s₁ s₂ : list A) (t₂_eq : a₂::t₂ = s₁++(a₁::s₂)), from ex,
  have dt₂'     : nodup (a₁::(s₁++s₂)), from nodup_head (by rewrite [t₂_eq at d₂]; exact d₂),
  have na₁s₁s₂  : a₁ ∉ s₁++s₂, from not_mem_of_nodup_cons dt₂',
  have na₁s₁    : a₁ ∉ s₁,     from not_mem_of_not_mem_append_left na₁s₁s₂,
  have na₁s₂    : a₁ ∉ s₂,     from not_mem_of_not_mem_append_right na₁s₁s₂,
  have ds₁s₂    : nodup (s₁++s₂), from nodup_of_nodup_cons dt₂',
  have eqv     : ∀a, a ∈ t₁ ↔ a ∈ s₁++s₂, from
    take a, iff.intro
      (λ aint₁   : a ∈ t₁,
         assert aina₂t₂ : a ∈ a₂::t₂,       from iff.mp (e a) (mem_cons_of_mem _ aint₁),
         have ains₁a₁s₂ : a ∈ s₁++(a₁::s₂), by rewrite [t₂_eq at aina₂t₂]; exact aina₂t₂,
         or.elim (mem_or_mem_of_mem_append ains₁a₁s₂)
           (λ ains₁ : a ∈ s₁, mem_append_left s₂ ains₁)
           (λ aina₁s₂ : a ∈ a₁::s₂, or.elim (eq_or_mem_of_mem_cons aina₁s₂)
             (λ aeqa₁ : a = a₁, absurd (aeqa₁ ▸ aint₁) na₁int₁)
             (λ ains₂ : a ∈ s₂, mem_append_right s₁ ains₂)))
      (λ ains₁s₂ : a ∈ s₁ ++ s₂, or.elim (mem_or_mem_of_mem_append ains₁s₂)
        (λ ains₁ : a ∈ s₁,
           have aina₂t₂ : a ∈ a₂::t₂, from by rewrite [t₂_eq]; exact (mem_append_left _ ains₁),
           have aina₁t₁ : a ∈ a₁::t₁, from iff.mp' (e a) aina₂t₂,
           or.elim (eq_or_mem_of_mem_cons aina₁t₁)
             (λ aeqa₁ : a = a₁, absurd (aeqa₁ ▸ ains₁) na₁s₁)
             (λ aint₁ : a ∈ t₁, aint₁))
        (λ ains₂ : a ∈ s₂,
           have aina₂t₂ : a ∈ a₂::t₂, from by rewrite [t₂_eq]; exact (mem_append_right _ (mem_cons_of_mem _ ains₂)),
           have aina₁t₁ : a ∈ a₁::t₁, from iff.mp' (e a) aina₂t₂,
           or.elim (eq_or_mem_of_mem_cons aina₁t₁)
             (λ aeqa₁ : a = a₁, absurd (aeqa₁ ▸ ains₂) na₁s₂)
             (λ aint₁ : a ∈ t₁, aint₁))),
  calc a₁::t₁ ~ a₁::(s₁++s₂) : skip a₁ (perm_ext dt₁ ds₁s₂ eqv)
         ...  ~ s₁++(a₁::s₂) : !perm_middle
         ...  = a₂::t₂       : by rewrite t₂_eq
end ext

/- cross_product -/
section cross_product
theorem perm_cross_product_left {l₁ l₂ : list A} (t₁ : list B) : l₁ ~ l₂ → (cross_product l₁ t₁) ~ (cross_product l₂ t₁) :=
assume p : l₁ ~ l₂, perm.induction_on p
  !perm.refl
  (λ x l₁ l₂ p r, perm_app !perm.refl r)
  (λ x y l,
    let m₁ := map (λ b, (x, b)) t₁ in
    let m₂ := map (λ b, (y, b)) t₁ in
    let c  := cross_product l t₁ in
    calc m₂ ++ (m₁ ++ c) = (m₂ ++ m₁) ++ c  : by rewrite append.assoc
                     ... ~ (m₁ ++ m₂) ++ c  : perm_app !perm_app_comm !perm.refl
                     ... =  m₁ ++ (m₂ ++ c) : by rewrite append.assoc)
  (λ l₁ l₂ l₃ p₁ p₂ r₁ r₂, trans r₁ r₂)

theorem perm_cross_product_right (l : list A) {t₁ t₂ : list B} : t₁ ~ t₂ → (cross_product l t₁) ~ (cross_product l t₂) :=
list.induction_on l
  (λ p, by rewrite [*nil_cross_product]; exact !perm.refl)
  (λ a t r p,
    perm_app (perm_map _ p) (r p))

theorem perm_cross_product {l₁ l₂ : list A} {t₁ t₂ : list B} : l₁ ~ l₂ → t₁ ~ t₂ → (cross_product l₁ t₁) ~ (cross_product l₂ t₂) :=
assume p₁ p₂, trans (perm_cross_product_left t₁ p₁) (perm_cross_product_right l₂ p₂)
end cross_product
end perm
