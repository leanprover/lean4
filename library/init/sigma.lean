-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura, Jeremy Avigad, Floris van Doorn
prelude
import init.num init.wf init.logic init.tactic

structure sigma {A : Type} (B : A → Type) :=
dpair :: (dpr1 : A) (dpr2 : B dpr1)

notation `Σ` binders `,` r:(scoped P, sigma P) := r

namespace sigma

  notation `dpr₁` := dpr1
  notation `dpr₂` := dpr2

  namespace ops
  postfix `.1`:(max+1) := dpr1
  postfix `.2`:(max+1) := dpr2
  notation `⟨` t:(foldr `,` (e r, sigma.dpair e r)) `⟩`:0 := t --input ⟨ ⟩ as \< \>
  end ops

  open well_founded

  section
  variables {A : Type} {B : A → Type}
  variable  (Ra  : A → A → Prop)
  variable  (Rb  : ∀ a, B a → B a → Prop)

  -- Lexicographical order based on Ra and Rb
  inductive lex : sigma B → sigma B → Prop :=
  left  : ∀{a₁ b₁} a₂ b₂, Ra a₁ a₂   → lex (dpair a₁ b₁) (dpair a₂ b₂),
  right : ∀a {b₁ b₂},     Rb a b₁ b₂ → lex (dpair a b₁)  (dpair a b₂)
  end

  context
  parameters {A : Type} {B : A → Type}
  parameters {Ra  : A → A → Prop} {Rb : Π a : A, B a → B a → Prop}
  infix `≺`:50 := lex Ra Rb

  set_option pp.beta true

  variables {C : Πa, B a → Type} {D : Πa b, C a b → Type}
  variables {a a' : A}
            {b : B a} {b' : B a'}
            {c : C a b} {c' : C a' b'}
            {d : D a b c} {d' : D a' b' c'}

  private theorem hcongr_arg2 (f : Πa b, C a b) (Ha : a = a') (Hb : b == b') : f a b == f a' b' :=
  hcongr (hcongr_arg f Ha) (hcongr_arg C Ha) Hb

  private theorem hcongr_arg3 (f : Πa b c, D a b c) (Ha : a = a') (Hb : b == b') (Hc : c == c')
      : f a b c == f a' b' c' :=
  hcongr (hcongr_arg2 f Ha Hb) (hcongr_arg2 D Ha Hb) Hc

  definition lex.accessible {a} (aca : acc Ra a) (acb : ∀a, well_founded (Rb a)) : ∀ (b : B a), acc (lex Ra Rb) (dpair a b) :=
  acc.rec_on aca
    (λxa aca (iHa : ∀y, Ra y xa → ∀b : B y, acc (lex Ra Rb) (dpair y b)),
      λb : B xa, acc.rec_on (acb xa b)
        (λxb acb
          (iHb : ∀y, Rb xa y xb → acc (lex Ra Rb) (dpair xa y)),
          acc.intro (dpair xa xb) (λp (lt : p ≺ (dpair xa xb)),
            have aux : xa = xa → xb == xb → acc (lex Ra Rb) p, from
              @lex.rec_on A B Ra Rb (λp₁ p₂, dpr1 p₂ = xa → dpr2 p₂ == xb → acc (lex Ra Rb) p₁)
                         p (dpair xa xb) lt
                (λa₁ b₁ a₂ b₂ (H : Ra a₁ a₂) (eq₂ : a₂ = xa) (eq₃ : b₂ == xb),
                  show acc (lex Ra Rb) (dpair a₁ b₁), from
                  have Ra₁  : Ra a₁ xa, from eq.rec_on eq₂ H,
                  iHa a₁ Ra₁ b₁)
                (λa b₁ b₂ (H : Rb a b₁ b₂) (eq₂ : a = xa) (eq₃ : b₂ == xb),
                  -- TODO(Leo): cleanup this proof
                  show acc (lex Ra Rb) (dpair a b₁), from
                  let b₁' : B xa := eq.rec_on eq₂ b₁ in
                  have aux₁ : b₁ == b₁', from
                    heq.symm (eq_rec_heq eq₂ b₁),
                  have aux₂ : Rb a b₁ b₂ = Rb xa b₁' xb, from
                    heq.to_eq (hcongr_arg3 Rb eq₂ aux₁ eq₃),
                  have aux₃ : Rb xa b₁' xb, from
                    eq.rec_on aux₂ H,
                  have aux₄ : acc (lex Ra Rb) (dpair xa b₁'), from
                    iHb b₁' aux₃,
                  have aux₅ : ∀ (b₁ b₂ : B a) (H₁ : a = a) (H₂ : b₁ == b₂), acc (lex Ra Rb) (dpair a b₁) → acc (lex Ra Rb) (dpair a b₂), from
                    λ b₁ b₂ H₁ H₂ Ha, eq.rec_on (heq.to_eq H₂) Ha,
                  have aux₆ : ∀ (b₁ : B xa) (b₂ : B a) (H₁ : a = xa) (H₂ : b₁ == b₂), acc (lex Ra Rb) (dpair xa b₁) → acc (lex Ra Rb) (dpair a b₂), from
                    eq.rec_on eq₂ aux₅,
                  aux₆ b₁' b₁ eq₂ (heq.symm aux₁) aux₄),
            aux rfl !heq.refl)))

  -- The lexicographical order of well founded relations is well-founded
  definition lex.wf (Ha : well_founded Ra) (Hb : ∀ x, well_founded (Rb x)) : well_founded (lex Ra Rb) :=
  well_founded.intro (λp, destruct p (λa b, lex.accessible (Ha a) Hb b))

  end
end sigma
