/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: data.perm
Author: Leonardo de Moura

List permutations
-/
import data.list
open list setoid

variable {A : Type}

inductive perm : list A → list A → Prop :=
| nil   : perm [] []
| skip  : Π (x : A) {l₁ l₂ : list A}, perm l₁ l₂ → perm (x::l₁) (x::l₂)
| swap  : Π (x y : A) (l : list A), perm (y::x::l) (x::y::l)
| trans : Π {l₁ l₂ l₃ : list A}, perm l₁ l₂ → perm l₂ l₃ → perm l₁ l₃

namespace perm
  theorem eq_nil_of_perm_nil {l₁ : list A} (p : perm [] l₁) : l₁ = [] :=
  have gen : ∀ (l₂ : list A) (p : perm l₂ l₁), l₂ = [] → l₁ = [], from
    take l₂ p, perm.induction_on p
      (λ h, h)
      (λ x y l₁ l₂ p₁ r₁, list.no_confusion r₁)
      (λ x y l e, list.no_confusion e)
      (λ l₁ l₂ l₃ p₁ p₂ r₁ r₂ e, r₂ (r₁ e)),
  gen [] p rfl

  theorem not_perm_nil_cons (x : A) (l : list A) : ¬ perm [] (x::l) :=
  have gen : ∀ (l₁ l₂ : list A) (p : perm l₁ l₂), l₁ = [] → l₂ = (x::l) → false, from
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

  protected theorem refl : ∀ (l : list A), perm l l
  | []      := nil
  | (x::xs) := skip x (refl xs)

  protected theorem symm : ∀ {l₁ l₂ : list A}, perm l₁ l₂ → perm l₂ l₁ :=
  take l₁ l₂ p, perm.induction_on p
    nil
    (λ x l₁ l₂ p₁ r₁, skip x r₁)
    (λ x y l, swap y x l)
    (λ l₁ l₂ l₃ p₁ p₂ r₁ r₂, trans r₂ r₁)

  theorem is_eqv (A : Type) : equivalence (@perm A) :=
  mk_equivalence (@perm A) (@refl A) (@symm A) (@trans A)

  protected definition is_setoid [instance] (A : Type) : setoid (list A) :=
  setoid.mk (@perm A) (is_eqv A)

  theorem mem_perm (a : A) (l₁ l₂ : list A) : perm l₁ l₂ → a ∈ l₁ → a ∈ l₂ :=
  assume p, perm.induction_on p
    (λ h, h)
    (λ x l₁ l₂ p₁ r₁ i, or.elim i
      (λ aeqx, by rewrite aeqx; apply !mem_cons)
      (λ ainl₁ : a ∈ l₁, or.inr (r₁ ainl₁)))
    (λ x y l ainyxl, or.elim ainyxl
      (λ aeqy  : a = y, by rewrite aeqy; exact (or.inr !mem_cons))
      (λ ainxl : a ∈ x::l, or.elim ainxl
        (λ aeqx : a = x, or.inl aeqx)
        (λ ainl : a ∈ l, or.inr (or.inr ainl))))
    (λ l₁ l₂ l₃ p₁ p₂ r₁ r₂ ainl₁, r₂ (r₁ ainl₁))

  theorem perm_app_left {l₁ l₂ : list A} (t₁ : list A) : perm l₁ l₂ → perm (l₁++t₁) (l₂++t₁) :=
  assume p, perm.induction_on p
    !refl
    (λ x l₁ l₂ p₁ r₁, skip x r₁)
    (λ x y l, !swap)
    (λ l₁ l₂ l₃ p₁ p₂ r₁ r₂, trans r₁ r₂)

  theorem perm_app_right (l : list A) {t₁ t₂ : list A} : perm t₁ t₂ → perm (l++t₁) (l++t₂) :=
  list.induction_on l
    (λ p, p)
    (λ x xs r p, skip x (r p))

  theorem perm_app {l₁ l₂ t₁ t₂ : list A} : perm l₁ l₂ → perm t₁ t₂ → perm (l₁++t₁) (l₂++t₂) :=
  assume p₁ p₂, trans (perm_app_left t₁ p₁) (perm_app_right l₂ p₂)

  theorem perm_app_cons (a : A) {h₁ h₂ t₁ t₂ : list A} : perm h₁ h₂ → perm t₁ t₂ → perm (h₁ ++ (a::t₁)) (h₂ ++ (a::t₂)) :=
  assume p₁ p₂, perm_app p₁ (skip a p₂)

  theorem perm_cons_app (a : A) : ∀ (l : list A), perm (a::l) (l ++ [a])
  | []      := !refl
  | (x::xs) :=
    show perm (a::x::xs) (x::(xs ++ [a])),    from
    have p₁ : perm (a::xs) (xs++[a]),         from perm_cons_app xs,
    have p₂ : perm (x::a::xs) (x::(xs++[a])), from skip x p₁,
    have p₃ : perm (a::x::xs) (x::a::xs),     from swap x a xs,
    trans p₃ p₂

  theorem perm_app_comm {l₁ l₂ : list A} : perm (l₁++l₂) (l₂++l₁) :=
  list.induction_on l₁
    (by rewrite [append_nil_right, append_nil_left]; apply refl)
    (λ a t r,
      show perm (a::(t++l₂)) (l₂++(a::t)), from
      begin
        have p₀ : perm (a::(t++l₂)) (a::(l₂++t)),   from skip a r,
        have p₁ : perm (a::(l₂++t)) (l₂++t++[a]),   from !perm_cons_app,
        have p₂ : perm (t++[a]) (a::t),             from symm (perm_cons_app a t),
        have p₃ : perm (l₂++(t++[a])) (l₂++(a::t)), from perm_app_right l₂ p₂,
        rewrite [append.assoc at p₁],
        exact (trans p₀ (trans p₁ p₃))
      end)

  theorem length_eq_lenght_of_perm {l₁ l₂ : list A} : perm l₁ l₂ → length l₁ = length l₂ :=
  assume p, perm.induction_on p
    rfl
    (λ x l₁ l₂ p r, by rewrite [*length_cons, r])
    (λ x y l, by rewrite *length_cons)
    (λ l₁ l₂ l₃ p₁ p₂ r₁ r₂, eq.trans r₁ r₂)

  theorem eq_singlenton_of_perm_inv (a : A) {l : list A} : perm [a] l → l = [a] :=
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

  theorem eq_singlenton_of_perm (a b : A) : perm [a] [b] → a = b :=
  assume p, list.no_confusion (eq_singlenton_of_perm_inv a p) (λ e₁ e₂, by rewrite e₁)

  theorem perm_rev : ∀ (l : list A), perm l (reverse l)
  | []      := nil
  | (x::xs) :=
    begin
     rewrite [reverse_cons, concat_eq_append],
     apply (trans (perm_cons_app x xs)),
     exact (perm_app_left [x] (perm_rev xs))
    end
end perm
