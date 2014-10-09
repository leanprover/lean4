-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura, Jeremy Avigad
import logic.inhabited logic.eq logic.decidable

-- data.prod
-- =========

open inhabited decidable eq.ops

-- The cartesian product.
inductive prod (A B : Type) : Type :=
  mk : A → B → prod A B

definition pair := @prod.mk

namespace prod
infixr `×` := prod

-- notation for n-ary tuples
notation `(` h `,` t:(foldl `,` (e r, prod.mk r e) h) `)` := t

section
  parameters {A B : Type}
  protected theorem destruct {P : A × B → Prop} (p : A × B) (H : ∀a b, P (a, b)) : P p :=
  rec H p

  definition pr1 (p : prod A B) := rec (λ x y, x) p
  definition pr2 (p : prod A B) := rec (λ x y, y) p
  notation `pr₁`:max := pr1
  notation `pr₂`:max := pr2

  variables (a : A) (b : B)

  theorem pr1.pair : pr₁ (a, b) = a :=
  rfl

  theorem pr2.pair : pr₂ (a, b) = b :=
  rfl

  theorem prod_ext (p : prod A B) : pair (pr₁ p) (pr₂ p) = p :=
  destruct p (λx y, eq.refl (x, y))

  variables {a₁ a₂ : A} {b₁ b₂ : B}

  theorem pair_eq : a₁ = a₂ → b₁ = b₂ → (a₁, b₁) = (a₂, b₂) :=
  assume H1 H2, H1 ▸ H2 ▸ rfl

  protected theorem equal {p₁ p₂ : prod A B} : pr₁ p₁ = pr₁ p₂ → pr₂ p₁ = pr₂ p₂ → p₁ = p₂ :=
  destruct p₁ (take a₁ b₁, destruct p₂ (take a₂ b₂ H₁ H₂, pair_eq H₁ H₂))

  protected definition is_inhabited [instance] : inhabited A → inhabited B → inhabited (prod A B) :=
  take (H₁ : inhabited A) (H₂ : inhabited B),
    inhabited.destruct H₁ (λa, inhabited.destruct H₂ (λb, inhabited.mk (pair a b)))

  protected definition has_decidable_eq [instance] : decidable_eq A → decidable_eq B → decidable_eq (A × B) :=
  take (H₁ : decidable_eq A) (H₂ : decidable_eq B) (u v : A × B),
    have H₃ : u = v ↔ (pr₁ u = pr₁ v) ∧ (pr₂ u = pr₂ v), from
      iff.intro
        (assume H, H ▸ and.intro rfl rfl)
        (assume H, and.elim H (assume H₄ H₅, equal H₄ H₅)),
    decidable_iff_equiv _ (iff.symm H₃)
end
end prod
