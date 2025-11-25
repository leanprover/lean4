/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
prelude
public import Init.Grind.Tactics
public section
namespace Function

/--
Transforms a function from pairs into an equivalent two-parameter function.

Examples:
 * `Function.curry (fun (x, y) => x + y) 3 5 = 8`
 * `Function.curry Prod.swap 3 "five" = ("five", 3)`
-/
@[inline, expose]
def curry : (α × β → φ) → α → β → φ := fun f a b => f (a, b)

/--
Transforms a two-parameter function into an equivalent function from pairs.

Examples:
 * `Function.uncurry List.drop (1, ["a", "b", "c"]) = ["b", "c"]`
 * `[("orange", 2), ("android", 3) ].map (Function.uncurry String.take) = ["or", "and"]`
-/
@[inline, expose]
def uncurry : (α → β → φ) → α × β → φ := fun f a => f a.1 a.2

@[simp, grind =]
theorem curry_uncurry (f : α → β → φ) : curry (uncurry f) = f :=
  rfl

@[simp, grind =]
theorem uncurry_curry (f : α × β → φ) : uncurry (curry f) = f :=
  funext fun ⟨_a, _b⟩ => rfl

@[simp, grind =]
theorem uncurry_apply_pair {α β γ} (f : α → β → γ) (x : α) (y : β) : uncurry f (x, y) = f x y :=
  rfl

@[simp, grind =]
theorem curry_apply {α β γ} (f : α × β → γ) (x : α) (y : β) : curry f x y = f (x, y) :=
  rfl

/-- A function `f : α → β` is called injective if `f x = f y` implies `x = y`. -/
@[expose]
def Injective (f : α → β) : Prop :=
  ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂

theorem Injective.comp {α β γ} {g : β → γ} {f : α → β} (hg : Injective g) (hf : Injective f) :
    Injective (g ∘ f) := fun _a₁ _a₂ => fun h => hf (hg h)

/-- A function `f : α → β` is called surjective if every `b : β` is equal to `f a`
for some `a : α`. -/
@[expose]
def Surjective (f : α → β) : Prop :=
  ∀ b, Exists fun a => f a = b

theorem Surjective.comp {α β γ} {g : β → γ} {f : α → β} (hg : Surjective g) (hf : Surjective f) :
    Surjective (g ∘ f) := fun c : γ =>
  Exists.elim (hg c) fun b hb =>
    Exists.elim (hf b) fun a ha =>
      Exists.intro a (show g (f a) = c from Eq.trans (congrArg g ha) hb)

/-- `LeftInverse g f` means that `g` is a left inverse to `f`. That is, `g ∘ f = id`. -/
@[expose, grind]
def LeftInverse {α β} (g : β → α) (f : α → β) : Prop :=
  ∀ x, g (f x) = x

/-- `HasLeftInverse f` means that `f` has an unspecified left inverse. -/
@[expose]
def HasLeftInverse {α β} (f : α → β) : Prop :=
  Exists fun finv : β → α => LeftInverse finv f

/-- `RightInverse g f` means that `g` is a right inverse to `f`. That is, `f ∘ g = id`. -/
@[expose, grind]
def RightInverse {α β} (g : β → α) (f : α → β) : Prop :=
  LeftInverse f g

/-- `HasRightInverse f` means that `f` has an unspecified right inverse. -/
@[expose]
def HasRightInverse {α β} (f : α → β) : Prop :=
  Exists fun finv : β → α => RightInverse finv f

theorem LeftInverse.injective {α β} {g : β → α} {f : α → β} : LeftInverse g f → Injective f :=
  fun h a b faeqfb => ((h a).symm.trans (congrArg g faeqfb)).trans (h b)

theorem HasLeftInverse.injective {α β} {f : α → β} : HasLeftInverse f → Injective f := fun h =>
  Exists.elim h fun _finv inv => inv.injective

theorem rightInverse_of_injective_of_leftInverse {α β} {f : α → β} {g : β → α} (injf : Injective f)
    (lfg : LeftInverse f g) : RightInverse f g := fun x =>
  have h : f (g (f x)) = f x := lfg (f x)
  injf h

theorem RightInverse.surjective {α β} {f : α → β} {g : β → α} (h : RightInverse g f) : Surjective f :=
  fun y => ⟨g y, h y⟩

theorem HasRightInverse.surjective {α β} {f : α → β} : HasRightInverse f → Surjective f
  | ⟨_finv, inv⟩ => inv.surjective

theorem leftInverse_of_surjective_of_rightInverse {α β} {f : α → β} {g : β → α} (surjf : Surjective f)
    (rfg : RightInverse f g) : LeftInverse f g := fun y =>
  Exists.elim (surjf y) fun x hx => ((hx ▸ rfl : f (g y) = f (g (f x))).trans (Eq.symm (rfg x) ▸ rfl)).trans hx

theorem injective_id : Injective (@id α) := fun _a₁ _a₂ h => h

theorem surjective_id : Surjective (@id α) := fun a => ⟨a, rfl⟩

variable {f : α → β}

theorem Injective.eq_iff (I : Injective f) {a b : α} : f a = f b ↔ a = b :=
  ⟨@I _ _, congrArg f⟩

theorem Injective.eq_iff' (I : Injective f) {a b : α} {c : β} (h : f b = c) : f a = c ↔ a = b :=
  h ▸ I.eq_iff

theorem Injective.ne (hf : Injective f) {a₁ a₂ : α} : a₁ ≠ a₂ → f a₁ ≠ f a₂ :=
  mt fun h ↦ hf h

theorem Injective.ne_iff (hf : Injective f) {x y : α} : f x ≠ f y ↔ x ≠ y :=
  ⟨mt <| congrArg f, hf.ne⟩

theorem Injective.ne_iff' (hf : Injective f) {x y : α} {z : β} (h : f y = z) : f x ≠ z ↔ x ≠ y :=
  h ▸ hf.ne_iff

protected theorem LeftInverse.id {α β} {g : β → α} {f : α → β} (h : LeftInverse g f) : g ∘ f = id :=
  funext h

protected theorem RightInverse.id {α β} {g : β → α} {f : α → β} (h : RightInverse g f) : f ∘ g = id :=
  funext h

end Function
