/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Extensional equality for functions, and a proof of function extensionality from quotients.
-/
prelude
import init.quot init.logic
set_option new_elaborator true

namespace function
  variables {A : Type} {B : A → Type}

  protected definition equiv (f₁ f₂ : Π x : A, B x) : Prop := ∀ x, f₁ x = f₂ x

  local infix `~` := function.equiv

  protected theorem equiv.refl (f : Π x : A, B x) : f ~ f := take x, rfl

  protected theorem equiv.symm {f₁ f₂ : Π x: A, B x} : f₁ ~ f₂ → f₂ ~ f₁ :=
  λ H x, eq.symm (H x)

  protected theorem equiv.trans {f₁ f₂ f₃ : Π x: A, B x} : f₁ ~ f₂ → f₂ ~ f₃ → f₁ ~ f₃ :=
  λ H₁ H₂ x, eq.trans (H₁ x) (H₂ x)

  protected theorem equiv.is_equivalence (A : Type) (B : A → Type) : equivalence (@function.equiv A B) :=
  mk_equivalence (@function.equiv A B) (@equiv.refl A B) (@equiv.symm A B) (@equiv.trans A B)
end function

section
  open quot
  variables {A : Type} {B : A → Type}

  attribute [instance]
  private definition fun_setoid (A : Type) (B : A → Type) : setoid (Πx : A, B x) :=
  setoid.mk (@function.equiv A B) (function.equiv.is_equivalence A B)

  private definition extfun (A : Type) (B : A → Type) : Type :=
  quot (fun_setoid A B)

  private definition fun_to_extfun (f : Π x : A, B x) : extfun A B :=
  ⟦f⟧
  private definition extfun_app (f : extfun A B) : Π x : A, B x :=
  take x,
  quot.lift_on f
    (λ f : Π x : A, B x, f x)
    (λ f₁ f₂ H, H x)

  theorem funext {f₁ f₂ : Π x : A, B x} : (∀ x, f₁ x = f₂ x) → f₁ = f₂ :=
  assume H, calc
     f₁ = extfun_app ⟦f₁⟧ : rfl
    ... = extfun_app ⟦f₂⟧ : @sound _ _ f₁ f₂ H ▸ rfl
    ... = f₂              : rfl
end

attribute funext [intro!]

local infix `~` := function.equiv

attribute [instance]
definition subsingleton_pi {A : Type} {B : A → Type} (H : ∀ a, subsingleton (B a)) :
  subsingleton (Π a, B a) :=
subsingleton.intro (take f₁ f₂,
  have eqv : f₁ ~ f₂, from
    take a, subsingleton.elim (f₁ a) (f₂ a),
  funext eqv)
