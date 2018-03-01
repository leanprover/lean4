/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Jeremy Avigad, Haitao Zhang

General operations on functions.
-/
prelude
import init.data.prod init.funext init.logic
universes u₁ u₂ u₃ u₄

namespace function
variables {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} {δ : Sort u₄} {ζ : Sort u₁}

@[inline, reducible] def comp (f : β → φ) (g : α → β) : α → φ :=
λ x, f (g x)

@[inline, reducible] def dcomp {β : α → Sort u₂} {φ : Π {x : α}, β x → Sort u₃}
  (f : Π {x : α} (y : β x), φ y) (g : Π x, β x) : Π x, φ (g x) :=
λ x, f (g x)

infixr  ` ∘ `      := function.comp
infixr  ` ∘' `:80  := function.dcomp

@[reducible] def comp_right (f : β → β → β) (g : α → β) : β → α → β :=
λ b a, f b (g a)

@[reducible] def comp_left (f : β → β → β) (g : α → β) : α → β → β :=
λ a b, f (g a) b

@[reducible] def on_fun (f : β → β → φ) (g : α → β) : α → α → φ :=
λ x y, f (g x) (g y)

@[reducible] def combine (f : α → β → φ) (op : φ → δ → ζ) (g : α → β → δ)
  : α → β → ζ :=
λ x y, op (f x y) (g x y)

@[reducible] def const (β : Sort u₂) (a : α) : β → α :=
λ x, a

@[reducible] def swap {φ : α → β → Sort u₃} (f : Π x y, φ x y) : Π y x, φ x y :=
λ y x, f x y

@[reducible] def app {β : α → Sort u₂} (f : Π x, β x) (x : α) : β x :=
f x

infixl  ` on `:2         := on_fun
notation f ` -[` op `]- ` g  := combine f op g

lemma left_id (f : α → β) : id ∘ f = f := rfl

lemma right_id (f : α → β) : f ∘ id = f := rfl

@[simp] lemma comp_app (f : β → φ) (g : α → β) (a : α) : (f ∘ g) a = f (g a) := rfl

lemma comp.assoc (f : φ → δ) (g : β → φ) (h : α → β) : (f ∘ g) ∘ h = f ∘ (g ∘ h) := rfl

@[simp] lemma comp.left_id (f : α → β) : id ∘ f = f := rfl

@[simp] lemma comp.right_id (f : α → β) : f ∘ id = f := rfl

lemma comp_const_right (f : β → φ) (b : β) : f ∘ (const α b) = const α (f b) := rfl

@[reducible] def injective (f : α → β) : Prop := ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂

lemma injective_comp {g : β → φ} {f : α → β} (hg : injective g) (hf : injective f) : injective (g ∘ f) :=
assume a₁ a₂, assume h, hf (hg h)

@[reducible] def surjective (f : α → β) : Prop := ∀ b, ∃ a, f a = b

lemma surjective_comp {g : β → φ} {f : α → β} (hg : surjective g) (hf : surjective f) : surjective (g ∘ f) :=
λ (c : φ), exists.elim (hg c) (λ b hb, exists.elim (hf b) (λ a ha,
  exists.intro a (show g (f a) = c, from (eq.trans (congr_arg g ha) hb))))

def bijective (f : α → β) := injective f ∧ surjective f

lemma bijective_comp {g : β → φ} {f : α → β} : bijective g → bijective f → bijective (g ∘ f)
| ⟨h_ginj, h_gsurj⟩ ⟨h_finj, h_fsurj⟩ := ⟨injective_comp h_ginj h_finj, surjective_comp h_gsurj h_fsurj⟩

-- g is a left inverse to f
def left_inverse (g : β → α) (f : α → β) : Prop := ∀ x, g (f x) = x

def has_left_inverse (f : α → β) : Prop := ∃ finv : β → α, left_inverse finv f

-- g is a right inverse to f
def right_inverse (g : β → α) (f : α → β) : Prop := left_inverse f g

def has_right_inverse (f : α → β) : Prop := ∃ finv : β → α, right_inverse finv f

lemma injective_of_left_inverse {g : β → α} {f : α → β} : left_inverse g f → injective f :=
assume h, assume a b, assume faeqfb,
have h₁ : a = g (f a),       from eq.symm (h a),
have h₂ : g (f b) = b,       from h b,
have h₃ : g (f a) = g (f b), from congr_arg g faeqfb,
eq.trans h₁ (eq.trans h₃ h₂)

lemma injective_of_has_left_inverse {f : α → β} : has_left_inverse f → injective f :=
assume h, exists.elim h (λ finv inv, injective_of_left_inverse inv)

lemma right_inverse_of_injective_of_left_inverse {f : α → β} {g : β → α}
    (injf : injective f) (lfg : left_inverse f g) :
  right_inverse f g :=
assume x,
have h : f (g (f x)) = f x, from lfg (f x),
injf h

lemma surjective_of_has_right_inverse {f : α → β} : has_right_inverse f → surjective f
| ⟨finv, inv⟩ b := ⟨finv b, inv b⟩

lemma left_inverse_of_surjective_of_right_inverse {f : α → β} {g : β → α}
    (surjf : surjective f) (rfg : right_inverse f g) :
  left_inverse f g :=
assume y, exists.elim (surjf y) (λ x hx, calc
  f (g y) = f (g (f x)) : hx ▸ rfl
      ... = f x         : eq.symm (rfg x) ▸ rfl
      ... = y           : hx)

lemma injective_id : injective (@id α) := assume a₁ a₂ h, h

lemma surjective_id : surjective (@id α) := assume a, ⟨a, rfl⟩

lemma bijective_id : bijective (@id α) := ⟨injective_id, surjective_id⟩

end function

namespace function
variables {α : Type u₁} {β : Type u₂} {φ : Type u₃}

@[inline] def curry : (α × β → φ) → α → β → φ :=
λ f a b, f (a, b)

@[inline] def uncurry : (α → β → φ) → α × β → φ :=
λ f ⟨a, b⟩, f a b

@[simp] lemma curry_uncurry (f : α → β → φ) : curry (uncurry f) = f :=
rfl

@[simp] lemma uncurry_curry (f : α × β → φ) : uncurry (curry f) = f :=
funext (λ ⟨a, b⟩, rfl)

def id_of_left_inverse {g : β → α} {f : α → β} : left_inverse g f → g ∘ f = id :=
assume h, funext h

def id_of_right_inverse {g : β → α} {f : α → β} : right_inverse g f → f ∘ g = id :=
assume h, funext h

end function
