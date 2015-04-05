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

theorem mem_perm (a : A) (l₁ l₂ : list A) : l₁ ~ l₂ → a ∈ l₁ → a ∈ l₂ :=
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
end perm
