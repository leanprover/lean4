/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Init.Data.List.Notation
import Init.SimpLemmas

@[expose] public section

/-! # State-indexed values -/

namespace Std.Do

/--
  A value indexed by a curried tuple of states.
  ```
  example : SVal [Nat, Bool] String = (Nat → Bool → String) := rfl
  ```
-/
abbrev SVal (σs : List (Type u)) (α : Type u) : Type u := match σs with
  | [] => α
  | σ :: σs => σ → SVal σs α
/- Note about the reducibility of SVal:
We need SVal to be reducible, otherwise type inference fails for `Triple`.
(Begs for investigation. #8074.)
-/

namespace SVal

/-- A tuple capturing the whole state of an `SVal`. -/
def StateTuple (σs : List (Type u)) : Type u := match σs with
  | [] => PUnit
  | σ :: σs => σ × StateTuple σs

instance : Inhabited (StateTuple []) where
  default := ()

instance [Inhabited σ] [Inhabited (StateTuple σs)] : Inhabited (StateTuple (σ :: σs)) where
  default := (default, default)

/-- Curry a function taking a `StateTuple` into an `SVal`. -/
def curry {σs : List (Type u)} (f : StateTuple σs → α) : SVal σs α := match σs with
  | [] => f ⟨⟩
  | _ :: _ => fun s => curry (fun s' => f (s, s'))
@[simp] theorem curry_nil {f : StateTuple [] → α} : curry f = f ⟨⟩ := rfl
@[simp] theorem curry_cons {σ : Type u} {σs : List (Type u)} {f : StateTuple (σ::σs) → α} {s : σ} : curry f s = curry (fun s' => f (s, s')) := rfl

/-- Uncurry an `SVal` into a function taking a `StateTuple`. -/
def uncurry {σs : List (Type u)} (f : SVal σs α) : StateTuple σs → α := match σs with
  | [] => fun _ => f
  | _ :: _ => fun (s, t) => uncurry (f s) t
@[simp] theorem uncurry_nil {σ : Type u} {s : σ} : uncurry (σs:=[]) s = fun _ => s := rfl
@[simp] theorem uncurry_cons {σ : Type u} {σs : List (Type u)} {f : SVal (σ::σs) α} {s : σ} {t : StateTuple σs} : uncurry f (s, t) = uncurry (f s) t := rfl

@[simp] theorem uncurry_curry {σs : List (Type u)} {f : StateTuple σs → α} : uncurry (σs:=σs) (curry f) = f := by induction σs <;> (simp[uncurry, curry, *]; rfl)
@[simp] theorem curry_uncurry {σs : List (Type u)} {f : SVal σs α} : curry (σs:=σs) (uncurry f) = f := by induction σs <;> simp[uncurry, curry, *]

/-- Embed a pure value into an `SVal`. -/
abbrev pure {σs : List (Type u)} (a : α) : SVal σs α := curry (fun _ => a)

instance [Inhabited α] : Inhabited (SVal σs α) where
  default := pure default

class GetTy (σ : Type u) (σs : List (Type u)) where
  get : SVal σs σ

instance : GetTy σ (σ :: σs) where
  get := fun s => pure s

instance [GetTy σ₁ σs] : GetTy σ₁ (σ₂ :: σs) where
  get := fun _ => GetTy.get

/-- Get the top-most state of type `σ` from an `SVal`. -/
def getThe {σs : List (Type u)} (σ : Type u) [GetTy σ σs] : SVal σs σ := GetTy.get
@[simp] theorem getThe_here {σs : List (Type u)} (σ : Type u) (s : σ) : getThe (σs := σ::σs) σ s = pure s := rfl
@[simp] theorem getThe_there {σs : List (Type u)} [GetTy σ σs] (σ' : Type u) (s : σ') : getThe (σs := σ'::σs) σ s = getThe (σs := σs) σ := rfl
