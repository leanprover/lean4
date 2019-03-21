/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Jeremy Avigad, Haitao Zhang

General operations on functions.
-/
prelude
import init.core
universes u₁ u₂ u₃ u₄

namespace Function
variables {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} {δ : Sort u₄} {ζ : Sort u₁}

@[inline, reducible] def comp (f : β → φ) (g : α → β) : α → φ :=
λ x, f (g x)

@[inline, reducible] def dcomp {β : α → Sort u₂} {φ : Π {x : α}, β x → Sort u₃}
  (f : Π {x : α} (y : β x), φ y) (g : Π x, β x) : Π x, φ (g x) :=
λ x, f (g x)

infixr  ` ∘ `      := Function.comp
infixr  ` ∘' `:80  := Function.dcomp

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

@[reducible] def Injective (f : α → β) : Prop := ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂

lemma injectiveComp {g : β → φ} {f : α → β} (hg : Injective g) (hf : Injective f) : Injective (g ∘ f) :=
assume a₁ a₂, assume h, hf (hg h)

@[reducible] def Surjective (f : α → β) : Prop := ∀ b, ∃ a, f a = b

lemma surjectiveComp {g : β → φ} {f : α → β} (hg : Surjective g) (hf : Surjective f) : Surjective (g ∘ f) :=
λ (c : φ), Exists.elim (hg c) (λ b hb, Exists.elim (hf b) (λ a ha,
  Exists.intro a (show g (f a) = c, from (Eq.trans (congrArg g ha) hb))))

def Bijective (f : α → β) := Injective f ∧ Surjective f

lemma bijectiveComp {g : β → φ} {f : α → β} : Bijective g → Bijective f → Bijective (g ∘ f)
| ⟨hGinj, hGsurj⟩ ⟨hFinj, hFsurj⟩ := ⟨injectiveComp hGinj hFinj, surjectiveComp hGsurj hFsurj⟩

-- g is a left inverse to f
def LeftInverse (g : β → α) (f : α → β) : Prop := ∀ x, g (f x) = x

def hasLeftInverse (f : α → β) : Prop := ∃ finv : β → α, LeftInverse finv f

-- g is a right inverse to f
def RightInverse (g : β → α) (f : α → β) : Prop := LeftInverse f g

def hasRightInverse (f : α → β) : Prop := ∃ finv : β → α, RightInverse finv f

lemma injectiveOfLeftInverse {g : β → α} {f : α → β} : LeftInverse g f → Injective f :=
assume h, assume a b, assume faeqfb,
have h₁ : a = g (f a),       from Eq.symm (h a),
have h₂ : g (f b) = b,       from h b,
have h₃ : g (f a) = g (f b), from congrArg g faeqfb,
Eq.trans h₁ (Eq.trans h₃ h₂)

lemma injectiveOfHasLeftInverse {f : α → β} : hasLeftInverse f → Injective f :=
assume h, Exists.elim h (λ finv inv, injectiveOfLeftInverse inv)

lemma rightInverseOfInjectiveOfLeftInverse {f : α → β} {g : β → α}
    (injf : Injective f) (lfg : LeftInverse f g) :
  RightInverse f g :=
assume x,
have h : f (g (f x)) = f x, from lfg (f x),
injf h

lemma surjectiveOfHasRightInverse {f : α → β} : hasRightInverse f → Surjective f
| ⟨finv, inv⟩ b := ⟨finv b, inv b⟩

lemma leftInverseOfSurjectiveOfRightInverse {f : α → β} {g : β → α}
    (surjf : Surjective f) (rfg : RightInverse f g) :
  LeftInverse f g :=
assume y, Exists.elim (surjf y) $ λ x hx,
  have h₁ : f (g y) = f (g (f x)), from hx ▸ rfl,
  have h₂ : f (g (f x)) = f x,     from Eq.symm (rfg x) ▸ rfl,
  have h₃ : f x = y,               from hx,
  Eq.trans h₁ $ Eq.trans h₂ h₃

lemma injectiveId : Injective (@id α) := assume a₁ a₂ h, h

lemma surjectiveId : Surjective (@id α) := assume a, ⟨a, rfl⟩

lemma bijectiveId : Bijective (@id α) := ⟨injectiveId, surjectiveId⟩

end Function

namespace Function
variables {α : Type u₁} {β : Type u₂} {φ : Type u₃}

@[inline] def curry : (α × β → φ) → α → β → φ :=
λ f a b, f (a, b)

@[inline] def uncurry : (α → β → φ) → α × β → φ :=
λ f ⟨a, b⟩, f a b

lemma curryUncurry (f : α → β → φ) : curry (uncurry f) = f :=
rfl

lemma uncurryCurry (f : α × β → φ) : uncurry (curry f) = f :=
funext (λ ⟨a, b⟩, rfl)

def idOfLeftInverse {g : β → α} {f : α → β} : LeftInverse g f → g ∘ f = id :=
assume h, funext h

def idOfRightInverse {g : β → α} {f : α → β} : RightInverse g f → f ∘ g = id :=
assume h, funext h

end Function
