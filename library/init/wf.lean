/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.relation init.tactic

inductive acc {A : Type} (R : A → A → Prop) : A → Prop :=
intro : ∀x, (∀ y, R y x → acc R y) → acc R x

namespace acc
  variables {A : Type} {R : A → A → Prop}

  definition inv {x y : A} (H₁ : acc R x) (H₂ : R y x) : acc R y :=
  acc.rec_on H₁ (λ x₁ ac₁ iH H₂, ac₁ y H₂) H₂

  -- dependent elimination for acc
  protected definition drec [recursor]
      {C : Π (a : A), acc R a → Type}
      (h₁ : Π (x : A) (acx : Π (y : A), R y x → acc R y),
              (Π (y : A) (ryx : R y x), C y (acx y ryx)) → C x (acc.intro x acx))
      {a : A} (h₂ : acc R a) : C a h₂ :=
  begin
    refine acc.rec _ h₂ h₂,
    intro x acx ih h₂,
    exact h₁ x acx (λ y ryx, ih y ryx (acx y ryx))
  end
end acc

inductive well_founded [class] {A : Type} (R : A → A → Prop) : Prop :=
intro : (∀ a, acc R a) → well_founded R

namespace well_founded
  definition apply [coercion] {A : Type} {R : A → A → Prop} (wf : well_founded R) : ∀a, acc R a :=
  take a, well_founded.rec_on wf (λp, p) a

  section
  parameters {A : Type} {R : A → A → Prop}
  local infix `≺`:50    := R

  hypothesis [Hwf : well_founded R]

  theorem recursion {C : A → Type} (a : A) (H : Πx, (Πy, y ≺ x → C y) → C x) : C a :=
  acc.rec_on (Hwf a) (λ x₁ ac₁ iH, H x₁ iH)

  theorem induction {C : A → Prop} (a : A) (H : ∀x, (∀y, y ≺ x → C y) → C x) : C a :=
  recursion a H

  variable {C : A → Type}
  variable F : Πx, (Πy, y ≺ x → C y) → C x

  definition fix_F (x : A) (a : acc R x) : C x :=
  acc.rec_on a (λ x₁ ac₁ iH, F x₁ iH)

  theorem fix_F_eq (x : A) (r : acc R x) :
    fix_F F x r = F x (λ (y : A) (p : y ≺ x), fix_F F y (acc.inv r p)) :=
  begin
    induction r using acc.drec,
    reflexivity -- proof is trivial due to proof irrelevance
  end
  end

  variables {A : Type} {C : A → Type} {R : A → A → Prop}

  -- Well-founded fixpoint
  definition fix [Hwf : well_founded R] (F : Πx, (Πy, R y x → C y) → C x) (x : A) : C x :=
  fix_F F x (Hwf x)

  -- Well-founded fixpoint satisfies fixpoint equation
  theorem fix_eq [Hwf : well_founded R] (F : Πx, (Πy, R y x → C y) → C x) (x : A) :
    fix F x = F x (λy h, fix F y) :=
  fix_F_eq F x (Hwf x)
end well_founded

open well_founded

-- Empty relation is well-founded
definition empty.wf {A : Type} : well_founded empty_relation :=
well_founded.intro (λ (a : A),
  acc.intro a (λ (b : A) (lt : false), false.rec _ lt))

-- Subrelation of a well-founded relation is well-founded
namespace subrelation
section
  parameters {A : Type} {R Q : A → A → Prop}
  parameters (H₁ : subrelation Q R)
  parameters (H₂ : well_founded R)

  definition accessible {a : A} (ac : acc R a) : acc Q a :=
  using H₁,
  begin
    induction ac with x ax ih, constructor,
    exact λ (y : A) (lt : Q y x), ih y (H₁ lt)
  end

  definition wf : well_founded Q :=
  well_founded.intro (λ a, accessible (H₂ a))
end
end subrelation

-- The inverse image of a well-founded relation is well-founded
namespace inv_image
section
  parameters {A B : Type} {R : B → B → Prop}
  parameters (f : A → B)
  parameters (H : well_founded R)

  private definition acc_aux {b : B} (ac : acc R b) : ∀ x, f x = b → acc (inv_image R f) x :=
  begin
    induction ac with x acx ih,
    intro z e, constructor,
    intro y lt, subst x,
    exact ih (f y) lt y rfl
  end

  definition accessible {a : A} (ac : acc R (f a)) : acc (inv_image R f) a :=
  acc_aux ac a rfl

  definition wf : well_founded (inv_image R f) :=
  well_founded.intro (λ a, accessible (H (f a)))
end
end inv_image

-- The transitive closure of a well-founded relation is well-founded
namespace tc
section
  parameters {A : Type} {R : A → A → Prop}
  local notation `R⁺` := tc R

  definition accessible {z} (ac: acc R z) : acc R⁺ z :=
  begin
    induction ac with x acx ih,
    constructor, intro y rel,
    induction rel with a b rab a b c rab rbc ih₁ ih₂,
      {exact ih a rab},
      {exact acc.inv (ih₂ acx ih) rab}
  end

  definition wf (H : well_founded R) : well_founded R⁺ :=
  well_founded.intro (λ a, accessible (H a))
end
end tc
