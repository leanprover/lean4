/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Jeremy Avigad, Haitao Zhang

General operations on functions.
-/
prelude
import init.prod init.funext init.logic

notation f ` $ `:1 a:1 := f a

variables {A : Type} {B : Type} {C : Type} {D : Type} {E : Type}

attribute [inline] [reducible] [unfold_full]
definition function.comp (f : B → C) (g : A → B) : A → C :=
λx, f (g x)

attribute [inline] [reducible] [unfold_full]
definition function.dcomp {B : A → Type} {C : Π {x : A}, B x → Type}
  (f : Π {x : A} (y : B x), C y) (g : Πx, B x) : Πx, C (g x) :=
λx, f (g x)

infixr  ` ∘ `      := function.comp
infixr  ` ∘' `:80  := function.dcomp

namespace function

attribute [reducible] [unfold_full]
definition comp_right (f : B → B → B) (g : A → B) : B → A → B :=
λ b a, f b (g a)

attribute [reducible] [unfold_full]
definition comp_left (f : B → B → B) (g : A → B) : A → B → B :=
λ a b, f (g a) b

attribute [reducible] [unfold_full]
definition on_fun (f : B → B → C) (g : A → B) : A → A → C :=
λx y, f (g x) (g y)

attribute [reducible] [unfold_full]
definition combine (f : A → B → C) (op : C → D → E) (g : A → B → D)
  : A → B → E :=
λx y, op (f x y) (g x y)

attribute [reducible] [unfold_full]
definition const (B : Type) (a : A) : B → A :=
λx, a

attribute [reducible] [unfold_full]
definition swap {C : A → B → Type} (f : Πx y, C x y) : Πy x, C x y :=
λy x, f x y

attribute [reducible]
definition app {B : A → Type} (f : Πx, B x) (x : A) : B x :=
f x

attribute [reducible] [unfold_full]
definition curry : (A × B → C) → A → B → C :=
λ f a b, f (a, b)

attribute [reducible] [unfold 5]
definition uncurry : (A → B → C) → (A × B → C) :=
λ f p, match p with (a, b) := f a b end

theorem curry_uncurry (f : A → B → C) : curry (uncurry f) = f :=
rfl

theorem uncurry_curry (f : A × B → C) : uncurry (curry f) = f :=
funext (λ p, match p with (a, b) := rfl end)

infixl  ` on `:1         := on_fun
notation f ` -[` op `]- ` g  := combine f op g

lemma left_id (f : A → B) : id ∘ f = f := rfl

lemma right_id (f : A → B) : f ∘ id = f := rfl

theorem comp.assoc (f : C → D) (g : B → C) (h : A → B) : (f ∘ g) ∘ h = f ∘ (g ∘ h) := rfl

theorem comp.left_id (f : A → B) : id ∘ f = f := rfl

theorem comp.right_id (f : A → B) : f ∘ id = f := rfl

theorem comp_const_right (f : B → C) (b : B) : f ∘ (const A b) = const A (f b) := rfl

attribute [reducible]
definition injective (f : A → B) : Prop := ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂

theorem injective_comp {g : B → C} {f : A → B} (Hg : injective g) (Hf : injective f) :
  injective (g ∘ f) :=
take a₁ a₂, assume Heq, Hf (Hg Heq)

attribute [reducible]
definition surjective (f : A → B) : Prop := ∀ b, ∃ a, f a = b

theorem surjective_comp {g : B → C} {f : A → B} (Hg : surjective g) (Hf : surjective f) :
  surjective (g ∘ f) :=
take (c : C), exists.elim (Hg c) (λ b Hb, exists.elim (Hf b) (λ a Ha,
  exists.intro a (eq.trans (congr_arg g Ha) Hb)))

definition bijective (f : A → B) := injective f ∧ surjective f

theorem bijective_comp {g : B → C} {f : A → B} (Hg : bijective g) (Hf : bijective f) :
  bijective (g ∘ f) :=
and.elim Hg (λ Hginj Hgsurj, and.elim Hf (λ Hfinj Hfsurj,
  and.intro (injective_comp Hginj Hfinj) (surjective_comp Hgsurj Hfsurj)))

-- g is a left inverse to f
definition left_inverse (g : B → A) (f : A → B) : Prop := ∀x, g (f x) = x

definition id_of_left_inverse {g : B → A} {f : A → B} : left_inverse g f → g ∘ f = id :=
assume h, funext h

definition has_left_inverse (f : A → B) : Prop := ∃ finv : B → A, left_inverse finv f

-- g is a right inverse to f
definition right_inverse (g : B → A) (f : A → B) : Prop := left_inverse f g

definition id_of_right_inverse {g : B → A} {f : A → B} : right_inverse g f → f ∘ g = id :=
assume h, funext h

definition has_right_inverse (f : A → B) : Prop := ∃ finv : B → A, right_inverse finv f

theorem injective_of_left_inverse {g : B → A} {f : A → B} : left_inverse g f → injective f :=
assume h, take a b, assume faeqfb,
have h₁ : a = g (f a),       from eq.symm (h a),
have h₂ : g (f b) = b,       from h b,
have h₃ : g (f a) = g (f b), from congr_arg g faeqfb,
eq.trans h₁ (eq.trans h₃ h₂)

theorem injective_of_has_left_inverse {f : A → B} : has_left_inverse f → injective f :=
assume h, exists.elim h (λ finv inv, injective_of_left_inverse inv)

theorem right_inverse_of_injective_of_left_inverse {f : A → B} {g : B → A}
    (injf : injective f) (lfg : left_inverse f g) :
  right_inverse f g :=
take x,
have H : f (g (f x)) = f x, from lfg (f x),
injf H

theorem surjective_of_has_right_inverse {f : A → B} : has_right_inverse f → surjective f :=
assume h, take b,
exists.elim h (λ finv inv,
let  a : A := finv b in
have h : f a = b, from calc
  f a  = f (finv b)   : rfl
   ... = b            : eq.subst (inv b) rfl,
exists.intro a h)

theorem left_inverse_of_surjective_of_right_inverse {f : A → B} {g : B → A}
    (surjf : surjective f) (rfg : right_inverse f g) :
  left_inverse f g :=
take y, exists.elim (surjf y) (λ x Hx,
calc
  f (g y) = f (g (f x)) : eq.subst Hx rfl
      ... = f x         : eq.subst (rfg x) rfl
      ... = y           : Hx)

theorem injective_id : injective (@id A) := take a₁ a₂ H, H

theorem surjective_id : surjective (@id A) := take a, exists.intro a rfl

theorem bijective_id : bijective (@id A) := and.intro injective_id surjective_id

end function
