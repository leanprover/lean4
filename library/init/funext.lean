/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: init.funext
Author: Jeremy Avigad

Function extensionality follows from quotients.
-/
prelude
import init.quot init.logic

section
  open quot
  variables {A : Type} {B : A → Type}

  private definition fun_eqv (f₁ f₂ : Πx : A, B x) : Prop := ∀x, f₁ x = f₂ x

  infix `~` := fun_eqv

  private theorem fun_eqv.refl (f : Πx : A, B x) : f ~ f := take x, rfl

  private theorem fun_eqv.symm {f₁ f₂ : Πx: A, B x} : f₁ ~ f₂ → f₂ ~ f₁ :=
  λH x, eq.symm (H x)

  private theorem fun_eqv.trans {f₁ f₂ f₃ : Πx: A, B x} : f₁ ~ f₂ → f₂ ~ f₃ → f₁ ~ f₃ :=
  λH₁ H₂ x, eq.trans (H₁ x) (H₂ x)

  private theorem fun_eqv.is_equivalence (A : Type) (B : A → Type) : equivalence (@fun_eqv A B) :=
  mk_equivalence (@fun_eqv A B) (@fun_eqv.refl A B) (@fun_eqv.symm A B) (@fun_eqv.trans A B)

  definition fun_setoid [instance] (A : Type) (B : A → Type) : setoid (Πx : A, B x) :=
  setoid.mk (@fun_eqv A B) (fun_eqv.is_equivalence A B)

  definition extfun (A : Type) (B : A → Type) : Type :=
  quot (fun_setoid A B)

  definition fun_to_extfun (f : Πx : A, B x) : extfun A B :=
  ⟦f⟧

  definition extfun_app (f : extfun A B) : Πx : A, B x :=
  take x,
  quot.lift_on f
    (λf : Πx : A, B x, f x)
    (λf₁ f₂ H, H x)

  theorem funext {f₁ f₂ : Πx : A, B x} : (∀x, f₁ x = f₂ x) → f₁ = f₂ :=
  assume H, calc
     f₁ = extfun_app ⟦f₁⟧      : rfl
    ... = extfun_app ⟦f₂⟧      : {sound H}
    ... = f₂                   : rfl
end

definition subsingleton_pi [instance] {A : Type} {B : A → Type} (H : ∀ a, subsingleton (B a)) : subsingleton (Π a, B a) :=
subsingleton.intro (take f₁ f₂,
  have eqv : f₁ ~ f₂, from
    take a, subsingleton.elim (f₁ a) (f₂ a),
  funext eqv)
