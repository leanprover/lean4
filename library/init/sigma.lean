/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: init.sigma
Author: Leonardo de Moura, Jeremy Avigad, Floris van Doorn
-/
prelude
import init.datatypes init.num init.wf init.logic init.tactic

definition dpair := @sigma.mk
notation `Σ` binders `,` r:(scoped P, sigma P) := r
-- notation for n-ary tuples; input ⟨ ⟩ as \< \>
notation `⟨`:max t:(foldr `,` (e r, sigma.mk e r)) `⟩`:0 := t

namespace sigma
  notation `pr₁`  := pr1
  notation `pr₂`  := pr2

  namespace ops
  postfix `.1`:(max+1) := pr1
  postfix `.2`:(max+1) := pr2
  end ops

  open ops well_founded

  section
  variables {A : Type} {B : A → Type}
  variable  (Ra  : A → A → Prop)
  variable  (Rb  : ∀ a, B a → B a → Prop)

  -- Lexicographical order based on Ra and Rb
  inductive lex : sigma B → sigma B → Prop :=
  left  : ∀{a₁ b₁} a₂ b₂, Ra a₁ a₂   → lex ⟨a₁, b₁⟩ ⟨a₂, b₂⟩,
  right : ∀a {b₁ b₂},     Rb a b₁ b₂ → lex ⟨a, b₁⟩  ⟨a, b₂⟩
  end

  context
  parameters {A : Type} {B : A → Type}
  parameters {Ra  : A → A → Prop} {Rb : Π a : A, B a → B a → Prop}
  infix `≺`:50 := lex Ra Rb

  definition lex.accessible {a} (aca : acc Ra a) (acb : ∀a, well_founded (Rb a)) : ∀ (b : B a), acc (lex Ra Rb) ⟨a, b⟩ :=
  acc.rec_on aca
    (λxa aca (iHa : ∀y, Ra y xa → ∀b : B y, acc (lex Ra Rb) ⟨y, b⟩),
      λb : B xa, acc.rec_on (acb xa b)
        (λxb acb
          (iHb : ∀ (y : B xa), Rb xa y xb → acc (lex Ra Rb) ⟨xa, y⟩),
          acc.intro ⟨xa, xb⟩ (λp (lt : p ≺ ⟨xa, xb⟩),
            have aux : xa = xa → xb == xb → acc (lex Ra Rb) p, from
              @lex.rec_on A B Ra Rb (λp₁ p₂, p₂.1 = xa → p₂.2 == xb → acc (lex Ra Rb) p₁)
                         p ⟨xa, xb⟩ lt
                (λ (a₁ : A) (b₁ : B a₁) (a₂ : A) (b₂ : B a₂) (H : Ra a₁ a₂) (eq₂ : a₂ = xa) (eq₃ : b₂ == xb),
                  begin cases eq₂, exact (iHa a₁ H b₁) end)
                (λ (a : A) (b₁ b₂ : B a) (H : Rb a b₁ b₂) (eq₂ : a = xa) (eq₃ : b₂ == xb),
                  begin cases eq₂, cases eq₃, exact (iHb b₁ H) end),
            aux rfl !heq.refl)))

  -- The lexicographical order of well founded relations is well-founded
  definition lex.wf (Ha : well_founded Ra) (Hb : ∀ x, well_founded (Rb x)) : well_founded (lex Ra Rb) :=
  well_founded.intro (λp, destruct p (λa b, lex.accessible (Ha a) Hb b))

  end
end sigma
