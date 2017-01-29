/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Extensional equality for functions, and a proof of function extensionality from quotients.
-/
prelude
import init.data.quot init.logic

universe variables u v

namespace function
variables {α : Type u} {β : α → Type v}

protected def equiv (f₁ f₂ : Π x : α, β x) : Prop := ∀ x, f₁ x = f₂ x

local infix `~` := function.equiv

protected theorem equiv.refl (f : Π x : α, β x) : f ~ f := take x, rfl

protected theorem equiv.symm {f₁ f₂ : Π x: α, β x} : f₁ ~ f₂ → f₂ ~ f₁ :=
λ h x, eq.symm (h x)

protected theorem equiv.trans {f₁ f₂ f₃ : Π x: α, β x} : f₁ ~ f₂ → f₂ ~ f₃ → f₁ ~ f₃ :=
λ h₁ h₂ x, eq.trans (h₁ x) (h₂ x)

protected theorem equiv.is_equivalence (α : Type u) (β : α → Type v) : equivalence (@function.equiv α β) :=
mk_equivalence (@function.equiv α β) (@equiv.refl α β) (@equiv.symm α β) (@equiv.trans α β)
end function

section
open quotient
variables {α : Type u} {β : α → Type v}

@[instance]
private def fun_setoid (α : Type u) (β : α → Type v) : setoid (Π x : α, β x) :=
setoid.mk (@function.equiv α β) (function.equiv.is_equivalence α β)

private def extfun (α : Type u) (β : α → Type v) : Type (max u v) :=
quotient (fun_setoid α β)

private def fun_to_extfun (f : Π x : α, β x) : extfun α β :=
⟦f⟧
private def extfun_app (f : extfun α β) : Π x : α, β x :=
take x,
quot.lift_on f
  (λ f : Π x : α, β x, f x)
  (λ f₁ f₂ h, h x)

theorem funext {f₁ f₂ : Π x : α, β x} : (∀ x, f₁ x = f₂ x) → f₁ = f₂ :=
assume h, calc
   f₁ = extfun_app ⟦f₁⟧ : rfl
  ... = extfun_app ⟦f₂⟧ : @sound _ _ f₁ f₂ h ▸ rfl
  ... = f₂              : rfl
end

attribute [intro!] funext

local infix `~` := function.equiv

instance pi.subsingleton {α : Type u} {β : α → Type v} [∀ a, subsingleton (β a)] : subsingleton (Π a, β a) :=
⟨λ f₁ f₂, funext (λ a, subsingleton.elim (f₁ a) (f₂ a))⟩
