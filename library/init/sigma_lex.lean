/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.sigma init.meta init.combinator
universe variables u v
namespace sigma
section
  variables {A : Type u} {B : A → Type v}
  variable  (Ra  : A → A → Prop)
  variable  (Rb  : ∀ a, B a → B a → Prop)

  -- Lexicographical order based on Ra and Rb
  inductive lex : sigma B → sigma B → Prop
  | left  : ∀ {a₁ : A} (b₁ : B a₁) {a₂ : A} (b₂ : B a₂), Ra a₁ a₂ → lex (sigma.mk a₁ b₁) (sigma.mk a₂ b₂)
  | right : ∀ (a : A)  {b₁ b₂ : B a}, Rb a b₁ b₂ → lex (sigma.mk a b₁)  (sigma.mk a b₂)
end

section
  open well_founded tactic
  parameters {A : Type u} {B : A → Type v}
  parameters {Ra  : A → A → Prop} {Rb : Π a : A, B a → B a → Prop}
  local infix `≺`:50 := lex Ra Rb

  def lex_accessible {a} (aca : acc Ra a) (acb : ∀ a, well_founded (Rb a))
                     : ∀ (b : B a), acc (lex Ra Rb) (sigma.mk a b) :=
  acc.rec_on aca
    (λ xa aca (iHa : ∀ y, Ra y xa → ∀ b : B y, acc (lex Ra Rb) (sigma.mk y b)),
      λ b : B xa, acc.rec_on (well_founded.apply (acb xa) b)
        (λ xb acb
          (iHb : ∀ (y : B xa), Rb xa y xb → acc (lex Ra Rb) (sigma.mk xa y)),
          acc.intro (sigma.mk xa xb) (λ p (lt : p ≺ (sigma.mk xa xb)),
            have aux : xa = xa → xb == xb → acc (lex Ra Rb) p, from
              @sigma.lex.rec_on A B Ra Rb (λ p₁ p₂, p₂.1 = xa → p₂.2 == xb → acc (lex Ra Rb) p₁)
                                p (sigma.mk xa xb) lt
                (λ (a₁ : A) (b₁ : B a₁) (a₂ : A) (b₂ : B a₂) (H : Ra a₁ a₂) (eq₂ : a₂ = xa) (eq₃ : b₂ == xb),
                  by do
                     get_local `eq₂ >>= subst,
                     to_expr `(iHa a₁ H b₁) >>= exact)
                (λ (a : A) (b₁ b₂ : B a) (H : Rb a b₁ b₂) (eq₂ : a = xa) (eq₃ : b₂ == xb),
                  by do
                    get_local `eq₂ >>= subst,
                    to_expr `(eq_of_heq eq₃) >>= note `new_eq₃,
                    get_local `new_eq₃ >>= subst,
                    to_expr `(iHb b₁ H) >>= exact),
            aux rfl (heq.refl xb))))

  -- The lexicographical order of well founded relations is well-founded
  def lex_wf (Ha : well_founded Ra) (Hb : ∀ x, well_founded (Rb x)) : well_founded (lex Ra Rb) :=
  well_founded.intro (λ p, destruct p (λ a b, lex_accessible (well_founded.apply Ha a) Hb b))
end

section
  parameters {A : Type u} {B : Type v}

  def lex_ndep (Ra : A → A → Prop) (Rb : B → B → Prop) :=
  lex Ra (λ a : A, Rb)

  def lex_ndep_wf {Ra  : A → A → Prop} {Rb : B → B → Prop} (Ha : well_founded Ra) (Hb : well_founded Rb)
                  : well_founded (lex_ndep Ra Rb) :=
  well_founded.intro (λ p, destruct p (λ a b, lex_accessible (well_founded.apply Ha a) (λ x, Hb) b))
end

section
  variables {A : Type u} {B : Type v}
  variable  (Ra  : A → A → Prop)
  variable  (Rb  : B → B → Prop)

  -- Reverse lexicographical order based on Ra and Rb
  inductive rev_lex : @sigma A (λ a, B) → @sigma A (λ a, B) → Prop
  | left  : ∀ {a₁ a₂ : A} (b : B), Ra a₁ a₂ → rev_lex (sigma.mk a₁ b) (sigma.mk a₂ b)
  | right : ∀ (a₁ : A) {b₁ : B} (a₂ : A) {b₂ : B}, Rb b₁ b₂ → rev_lex (sigma.mk a₁ b₁) (sigma.mk a₂ b₂)
end

section
  open well_founded tactic
  parameters {A : Type u} {B : Type v}
  parameters {Ra  : A → A → Prop} {Rb : B → B → Prop}
  local infix `≺`:50 := rev_lex Ra Rb

  def rev_lex_accessible {b} (acb : acc Rb b) (aca : ∀ a, acc Ra a): ∀ a, acc (rev_lex Ra Rb) (sigma.mk a b) :=
  acc.rec_on acb
    (λ xb acb (iHb : ∀ y, Rb y xb → ∀ a, acc (rev_lex Ra Rb) (sigma.mk a y)),
      λ a, acc.rec_on (aca a)
        (λ xa aca (iHa : ∀ y, Ra y xa → acc (rev_lex Ra Rb) (mk y xb)),
          acc.intro (sigma.mk xa xb) (λ p (lt : p ≺ (sigma.mk xa xb)),
            have aux : xa = xa → xb = xb → acc (rev_lex Ra Rb) p, from
              @rev_lex.rec_on A B Ra Rb (λ p₁ p₂, fst p₂ = xa → snd p₂ = xb → acc (rev_lex Ra Rb) p₁)
                              p (sigma.mk xa xb) lt
               (λ a₁ a₂ b (H : Ra a₁ a₂) (eq₂ : a₂ = xa) (eq₃ : b = xb),
                 show acc (rev_lex Ra Rb) (sigma.mk a₁ b), from
                 have Ra₁ : Ra a₁ xa, from eq.rec_on eq₂ H,
                 have aux : acc (rev_lex Ra Rb) (sigma.mk a₁ xb), from iHa a₁ Ra₁,
                 eq.rec_on (eq.symm eq₃) aux)
               (λ a₁ b₁ a₂ b₂ (H : Rb b₁ b₂) (eq₂ : a₂ = xa) (eq₃ : b₂ = xb),
                 show acc (rev_lex Ra Rb) (mk a₁ b₁), from
                 have Rb₁ : Rb b₁ xb, from eq.rec_on eq₃ H,
                 iHb b₁ Rb₁ a₁),
            aux rfl rfl)))

  def rev_lex_wf (Ha : well_founded Ra) (Hb : well_founded Rb) : well_founded (rev_lex Ra Rb) :=
  well_founded.intro (λ p, destruct p (λ a b, rev_lex_accessible (apply Hb b) (well_founded.apply Ha) a))
end

section
  def skip_left (A : Type u) {B : Type v} (Rb : B → B → Prop) : @sigma A (λ a, B) → @sigma A (λ a, B) → Prop :=
  rev_lex empty_relation Rb

  def skip_left_wf (A : Type u) {B : Type v} {Rb : B → B → Prop} (Hb : well_founded Rb) : well_founded (skip_left A Rb) :=
  rev_lex_wf empty_wf Hb

  def mk_skip_left {A : Type u} {B : Type v} {b₁ b₂ : B} {Rb : B → B → Prop}
                   (a₁ a₂ : A) (H : Rb b₁ b₂) : skip_left A Rb (sigma.mk a₁ b₁) (sigma.mk a₂ b₂) :=
  rev_lex.right _ _ _ H
end
end sigma
