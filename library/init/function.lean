/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Jeremy Avigad, Haitao Zhang

General operations on functions.
-/
prelude
import init.core
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

@[inline, reducible] def compRight (f : β → β → β) (g : α → β) : β → α → β :=
λ b a, f b (g a)

@[inline, reducible] def compLeft (f : β → β → β) (g : α → β) : α → β → β :=
λ a b, f (g a) b

@[inline, reducible] def onFun (f : β → β → φ) (g : α → β) : α → α → φ :=
λ x y, f (g x) (g y)

@[inline, reducible] def combine (f : α → β → φ) (op : φ → δ → ζ) (g : α → β → δ)
  : α → β → ζ :=
λ x y, op (f x y) (g x y)

@[inline, reducible] def const (β : Sort u₂) (a : α) : β → α :=
λ x, a

@[inline, reducible] def swap {φ : α → β → Sort u₃} (f : Π x y, φ x y) : Π y x, φ x y :=
λ y x, f x y

@[inline, reducible] def app {β : α → Sort u₂} (f : Π x, β x) (x : α) : β x :=
f x

infixl  ` on `:2         := onFun
notation f ` -[` op `]- ` g  := combine f op g

lemma leftId (f : α → β) : id ∘ f = f := rfl

lemma rightId (f : α → β) : f ∘ id = f := rfl

lemma compApp (f : β → φ) (g : α → β) (a : α) : (f ∘ g) a = f (g a) := rfl

lemma comp.assoc (f : φ → δ) (g : β → φ) (h : α → β) : (f ∘ g) ∘ h = f ∘ (g ∘ h) := rfl

lemma comp.leftId (f : α → β) : id ∘ f = f := rfl

lemma comp.rightId (f : α → β) : f ∘ id = f := rfl

lemma compConstRight (f : β → φ) (b : β) : f ∘ (const α b) = const α (f b) := rfl

@[reducible] def injective (f : α → β) : Prop := ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂

lemma injectiveComp {g : β → φ} {f : α → β} (hg : injective g) (hf : injective f) : injective (g ∘ f) :=
assume a₁ a₂, assume h, hf (hg h)

@[reducible] def surjective (f : α → β) : Prop := ∀ b, ∃ a, f a = b

lemma surjectiveComp {g : β → φ} {f : α → β} (hg : surjective g) (hf : surjective f) : surjective (g ∘ f) :=
λ (c : φ), exists.elim (hg c) (λ b hb, exists.elim (hf b) (λ a ha,
  exists.intro a (show g (f a) = c, from (eq.trans (congrArg g ha) hb))))

def bijective (f : α → β) := injective f ∧ surjective f

lemma bijectiveComp {g : β → φ} {f : α → β} : bijective g → bijective f → bijective (g ∘ f)
| ⟨hGinj, hGsurj⟩ ⟨hFinj, hFsurj⟩ := ⟨injectiveComp hGinj hFinj, surjectiveComp hGsurj hFsurj⟩

-- g is a left inverse to f
def leftInverse (g : β → α) (f : α → β) : Prop := ∀ x, g (f x) = x

def hasLeftInverse (f : α → β) : Prop := ∃ finv : β → α, leftInverse finv f

-- g is a right inverse to f
def rightInverse (g : β → α) (f : α → β) : Prop := leftInverse f g

def hasRightInverse (f : α → β) : Prop := ∃ finv : β → α, rightInverse finv f

lemma injectiveOfLeftInverse {g : β → α} {f : α → β} : leftInverse g f → injective f :=
assume h, assume a b, assume faeqfb,
have h₁ : a = g (f a),       from eq.symm (h a),
have h₂ : g (f b) = b,       from h b,
have h₃ : g (f a) = g (f b), from congrArg g faeqfb,
eq.trans h₁ (eq.trans h₃ h₂)

lemma injectiveOfHasLeftInverse {f : α → β} : hasLeftInverse f → injective f :=
assume h, exists.elim h (λ finv inv, injectiveOfLeftInverse inv)

lemma rightInverseOfInjectiveOfLeftInverse {f : α → β} {g : β → α}
    (injf : injective f) (lfg : leftInverse f g) :
  rightInverse f g :=
assume x,
have h : f (g (f x)) = f x, from lfg (f x),
injf h

lemma surjectiveOfHasRightInverse {f : α → β} : hasRightInverse f → surjective f
| ⟨finv, inv⟩ b := ⟨finv b, inv b⟩

lemma leftInverseOfSurjectiveOfRightInverse {f : α → β} {g : β → α}
    (surjf : surjective f) (rfg : rightInverse f g) :
  leftInverse f g :=
assume y, exists.elim (surjf y) $ λ x hx,
  have h₁ : f (g y) = f (g (f x)), from hx ▸ rfl,
  have h₂ : f (g (f x)) = f x,     from eq.symm (rfg x) ▸ rfl,
  have h₃ : f x = y,               from hx,
  eq.trans h₁ $ eq.trans h₂ h₃

lemma injectiveId : injective (@id α) := assume a₁ a₂ h, h

lemma surjectiveId : surjective (@id α) := assume a, ⟨a, rfl⟩

lemma bijectiveId : bijective (@id α) := ⟨injectiveId, surjectiveId⟩

end function

namespace function
variables {α : Type u₁} {β : Type u₂} {φ : Type u₃}

@[inline] def curry : (α × β → φ) → α → β → φ :=
λ f a b, f (a, b)

@[inline] def uncurry : (α → β → φ) → α × β → φ :=
λ f ⟨a, b⟩, f a b

lemma curryUncurry (f : α → β → φ) : curry (uncurry f) = f :=
rfl

lemma uncurryCurry (f : α × β → φ) : uncurry (curry f) = f :=
funext (λ ⟨a, b⟩, rfl)

def idOfLeftInverse {g : β → α} {f : α → β} : leftInverse g f → g ∘ f = id :=
assume h, funext h

def idOfRightInverse {g : β → α} {f : α → β} : rightInverse g f → f ∘ g = id :=
assume h, funext h

end function
