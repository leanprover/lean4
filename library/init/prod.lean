/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Jeremy Avigad
-/
prelude
import init.num init.wf

definition pair [constructor] := @prod.mk
notation A × B := prod A B
-- notation for n-ary tuples
notation `(` h `,` t:(foldl `,` (e r, prod.mk r e) h) `)` := t

namespace prod
  notation [parsing-only] A * B := prod A B
  namespace low_precedence_times
    reserve infixr [parsing-only] `*`:30     -- conflicts with notation for multiplication
    infixr `*` := prod
  end low_precedence_times

  notation `pr₁` := pr1
  notation `pr₂` := pr2

  namespace ops
  postfix `.1`:(max+1) := pr1
  postfix `.2`:(max+1) := pr2
  end ops

  definition destruct [reducible] := @prod.cases_on

  section
  variables {A B : Type}
  lemma pr1.mk (a : A) (b : B) : pr1 (mk a b) = a := rfl
  lemma pr2.mk (a : A) (b : B) : pr2 (mk a b) = b := rfl
  lemma eta : ∀ (p : A × B), mk (pr1 p) (pr2 p) = p
  | (a, b) := rfl
  end

  open well_founded

  section
  variables {A B : Type}
  variable  (Ra  : A → A → Prop)
  variable  (Rb  : B → B → Prop)

  -- Lexicographical order based on Ra and Rb
  inductive lex : A × B → A × B → Prop :=
  | left  : ∀{a₁ b₁} a₂ b₂, Ra a₁ a₂ → lex (a₁, b₁) (a₂, b₂)
  | right : ∀a {b₁ b₂},     Rb b₁ b₂ → lex (a, b₁)  (a, b₂)

  -- Relational product based on Ra and Rb
  inductive rprod : A × B → A × B → Prop :=
  intro : ∀{a₁ b₁ a₂ b₂}, Ra a₁ a₂ → Rb b₁ b₂ → rprod (a₁, b₁) (a₂, b₂)
  end

  section
  parameters {A B : Type}
  parameters {Ra  : A → A → Prop} {Rb  : B → B → Prop}
  local infix `≺`:50 := lex Ra Rb

  definition lex.accessible {a} (aca : acc Ra a) (acb : ∀b, acc Rb b): ∀b, acc (lex Ra Rb) (a, b) :=
  acc.rec_on aca
    (λxa aca (iHa : ∀y, Ra y xa → ∀b, acc (lex Ra Rb) (y, b)),
      λb, acc.rec_on (acb b)
        (λxb acb
          (iHb : ∀y, Rb y xb → acc (lex Ra Rb) (xa, y)),
          acc.intro (xa, xb) (λp (lt : p ≺ (xa, xb)),
            have aux : xa = xa → xb = xb → acc (lex Ra Rb) p, from
              @prod.lex.rec_on A B Ra Rb (λp₁ p₂, pr₁ p₂ = xa → pr₂ p₂ = xb → acc (lex Ra Rb) p₁)
                               p (xa, xb) lt
                (λa₁ b₁ a₂ b₂ (H : Ra a₁ a₂) (eq₂ : a₂ = xa) (eq₃ : b₂ = xb),
                  show acc (lex Ra Rb) (a₁, b₁), from
                  have Ra₁  : Ra a₁ xa, from eq.rec_on eq₂ H,
                  iHa a₁ Ra₁ b₁)
                (λa b₁ b₂ (H : Rb b₁ b₂) (eq₂ : a = xa) (eq₃ : b₂ = xb),
                  show acc (lex Ra Rb) (a, b₁), from
                  have Rb₁  : Rb b₁ xb, from eq.rec_on eq₃ H,
                  have eq₂' : xa = a, from eq.rec_on eq₂ rfl,
                  eq.rec_on eq₂' (iHb b₁ Rb₁)),
            aux rfl rfl)))

  -- The lexicographical order of well founded relations is well-founded
  definition lex.wf (Ha : well_founded Ra) (Hb : well_founded Rb) : well_founded (lex Ra Rb) :=
  well_founded.intro (λp, destruct p (λa b, lex.accessible (Ha a) (well_founded.apply Hb) b))

  -- Relational product is a subrelation of the lex
  definition rprod.sub_lex : ∀ a b, rprod Ra Rb a b → lex Ra Rb a b :=
  λa b H, prod.rprod.rec_on H (λ a₁ b₁ a₂ b₂ H₁ H₂, lex.left Rb a₂ b₂ H₁)

  -- The relational product of well founded relations is well-founded
  definition rprod.wf (Ha : well_founded Ra) (Hb : well_founded Rb) : well_founded (rprod Ra Rb) :=
  subrelation.wf (rprod.sub_lex) (lex.wf Ha Hb)

  end
end prod
