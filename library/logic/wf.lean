-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
import logic.eq

inductive acc {A : Type} (R : A → A → Prop) : A → Prop :=
intro : ∀x, (∀ y, R y x → acc R y) → acc R x

namespace acc
  variables {A : Type} {R : A → A → Prop}

  definition inv {x y : A} (H₁ : acc R x) (H₂ : R y x) : acc R y :=
  acc.rec_on H₁ (λ x₁ ac₁ iH H₂, ac₁ y H₂) H₂
end acc

inductive well_founded [class] {A : Type} (R : A → A → Prop) : Prop :=
intro : (∀ a, acc R a) → well_founded R

namespace well_founded
  definition apply [coercion] {A : Type} {R : A → A → Prop} (wf : well_founded R) : ∀a, acc R a :=
  take a, well_founded.rec_on wf (λp, p) a

  context
  parameters {A : Type} {R : A → A → Prop}
  infix `≺`:50    := R

  hypothesis [Hwf : well_founded R]

  theorem recursion {C : A → Type} (a : A) (H : Πx, (Πy, y ≺ x → C y) → C x) : C a :=
  acc.rec_on (Hwf a) (λ x₁ ac₁ iH, H x₁ iH)

  theorem indunction {C : A → Prop} (a : A) (H : ∀x, (∀y, y ≺ x → C y) → C x) : C a :=
  recursion a H

  variable {C : A → Type}
  variable F : Πx, (Πy, y ≺ x → C y) → C x

  definition fix_F (x : A) (a : acc R x) : C x :=
  acc.rec_on a (λ x₁ ac₁ iH, F x₁ iH)

  theorem fix_F_eq (x : A) (r : acc R x) :
    fix_F F x r = F x (λ (y : A) (p : y ≺ x), fix_F F y (acc.inv r p)) :=
  have gen : Π r : acc R x, fix_F F x r = F x (λ (y : A) (p : y ≺ x), fix_F F y (acc.inv r p)), from
  acc.rec_on r
    (λ x₁ ac iH (r₁ : acc R x₁),
      -- The proof is straightforward after we replace r₁ with acc.intro (to "unblock" evaluation).
      calc fix_F F x₁ r₁
           = fix_F F x₁ (acc.intro x₁ ac)             : proof_irrel r₁
       ... = F x₁ (λ y ay, fix_F F y (acc.inv r₁ ay)) : rfl),
  gen r
  end

  variables {A : Type} {C : A → Type} {R : A → A → Prop}

  -- Well-founded fixpoint
  definition fix [Hwf : well_founded R] (F : Πx, (Πy, R y x → C y) → C x) (x : A) : C x :=
  fix_F F x (Hwf x)

  -- Well-founded fixpoint satisfies fixpoint equation
  theorem fix_eq [Hwf : well_founded R] (F : Πx, (Πy, R y x → C y) → C x) (x : A) :
    fix F x = F x (λy h, fix F y) :=
  calc
    -- The proof is straightforward, it just uses fix_F_eq and proof irrelevance
    fix F x
        = F x (λy h, fix_F F y (acc.inv (Hwf x) h)) : fix_F_eq F x (Hwf x)
    ... = F x (λy h, fix F y)                       : rfl  -- proof irrelevance is used here

end well_founded
