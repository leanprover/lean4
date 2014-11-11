-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
import data.prod.decl logic.wf
open well_founded

namespace prod
  section
  variables {A B : Type}
  variable  (Ra  : A → A → Prop)
  variable  (Rb  : B → B → Prop)

  inductive lex : A × B → A × B → Prop :=
  left  : ∀a₁ b₁ a₂ b₂, Ra a₁ a₂ → lex (a₁, b₁) (a₂, b₂),
  right : ∀a b₁ b₂,     Rb b₁ b₂ → lex (a, b₁)  (a, b₂)
  end

  context
  parameters {A B : Type}
  parameters {Ra  : A → A → Prop} {Rb  : B → B → Prop}
  infix `≺`:50 := lex Ra Rb

  definition accessible {a} (aca : acc Ra a) (acb : ∀b, acc Rb b): ∀b, acc (lex Ra Rb) (a, b) :=
  acc.rec_on aca
    (λxa aca (iHa : ∀y, Ra y xa → ∀b, acc (lex Ra Rb) (y, b)),
      λb, acc.rec_on (acb b)
        (λxb acb
          (iHb : ∀y, Rb y xb → acc (lex Ra Rb) (xa, y)),
          acc.intro (xa, xb) (λp (lt : p ≺ (xa, xb)),
            have aux : xa = xa → xb = xb → acc (lex Ra Rb) p, from
              @lex.rec_on A B Ra Rb (λp₁ p₂, pr₁ p₂ = xa → pr₂ p₂ = xb → acc (lex Ra Rb) p₁)
                         p (xa, xb) lt
                (λa₁ b₁ a₂ b₂ (H : Ra a₁ a₂) (eq₂ : a₂ = xa) (eq₃ : b₂ = xb),
                  show acc (lex Ra Rb) (a₁, b₁), from
                  have Ra₁  : Ra a₁ xa, from eq.rec_on eq₂ H,
                  iHa a₁ Ra₁ b₁)
                (λa b₁ b₂ (H : Rb b₁ b₂) (eq₂ : a = xa) (eq₃ : b₂ = xb),
                  show acc (lex Ra Rb) (a, b₁), from
                  have Rb₁  : Rb b₁ xb, from eq.rec_on eq₃ H,
                  eq.rec_on (eq.symm eq₂) (iHb b₁ Rb₁)),
            aux rfl rfl)))

  -- The lexicographical order of well founded relations is well-founded
  definition wf (Ha : well_founded Ra) (Hb : well_founded Rb) : well_founded (lex Ra Rb) :=
  well_founded.intro (λp, destruct p (λa b, accessible (Ha a) (well_founded.apply Hb) b))

  end
end prod
