/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.Do.SPred

@[expose] public section

/-!
# Pre and postconditions

This module defines `Assertion` and `PostCond`, the types which constitute
the pre and postconditions of a Hoare triple in the program logic.

## Predicate shapes

Since `WP` supports arbitrary monads, `PostCond` must be general enough to
cope with state and exceptions.
For this reason, `PostCond` is indexed by a `PostShape` which is an abstraction
of the stack of effects supported by the monad, corresponding directly to
`StateT` and `ExceptT` layers in a transformer stack.
For every `StateT σ` effect, we get one `PostShape.arg σ` layer, whereas for every
`ExceptT ε` effect, we get one `PostShape.except ε` layer.
Currently, the only supported base layer is `PostShape.pure`.

## Pre and postconditions

The type of preconditions `Assertion ps` is distinct from the type of postconditions `PostCond α ps`.

This is because postconditions not only specify what happens upon successful termination of the
program, but also need to specify a property that holds upon failure.
We get one "barrel" for the success case, plus one barrel per `PostShape.except` layer.

It does not make much sense to talk about failure barrels in the context of preconditions.
Hence, `Assertion ps` is defined such that all `PostShape.except` layers are discarded from `ps`,
via `PostShape.args`.
-/

namespace Std.Do

universe u

inductive PostShape : Type (u+1) where
  | pure : PostShape
  | arg : (σ : Type u) → PostShape → PostShape
  | except : (ε : Type u) → PostShape → PostShape

variable {ps : PostShape.{u}} {α σ ε : Type u}

abbrev PostShape.args : PostShape.{u} → List (Type u)
  | .pure => []
  | .arg σ s => σ :: PostShape.args s
  | .except _ s => PostShape.args s

/--
  An assertion on the `.arg`s in the given predicate shape.
  ```
  example : Assertion (.arg ρ .pure) = (ρ → ULift Prop) := rfl
  example : Assertion (.except ε .pure) = ULift Prop := rfl
  example : Assertion (.arg σ (.except ε .pure)) = (σ → ULift Prop) := rfl
  example : Assertion (.except ε (.arg σ .pure)) = (σ → ULift Prop) := rfl
  ```
  This is an abbreviation for `SPred` under the hood, so all theorems about `SPred` apply.
-/
abbrev Assertion (ps : PostShape.{u}) : Type u :=
  SPred (PostShape.args ps)

/--
  Encodes one continuation barrel for each `PostShape.except` in the given predicate shape.
  ```
  example : FailConds (.pure) = Unit := rfl
  example : FailConds (.except ε .pure) = ((ε → ULift Prop) × Unit) := rfl
  example : FailConds (.arg σ (.except ε .pure)) = ((ε → ULift Prop) × Unit) := rfl
  example : FailConds (.except ε (.arg σ .pure)) = ((ε → σ → ULift Prop) × Unit) := rfl
  ```
-/
def FailConds : PostShape.{u} → Type u
  | .pure => PUnit
  | .arg _ ps => FailConds ps
  | .except ε ps => (ε → Assertion ps) × FailConds ps

@[simp]
def FailConds.const {ps : PostShape.{u}} (p : Prop) : FailConds ps := match ps with
  | .pure => ⟨⟩
  | .arg _ ps => @FailConds.const ps p
  | .except _ ps => (fun _ε => spred(⌜p⌝), @FailConds.const ps p)

@[simp]
def FailConds.true : FailConds ps := FailConds.const True

@[simp]
def FailConds.false : FailConds ps := FailConds.const False

instance : Inhabited (FailConds ps) where
  default := FailConds.true

def FailConds.entails {ps : PostShape.{u}} (x y : FailConds ps) : Prop :=
  match ps with
  | .pure => True
  | .arg _ ps => @entails ps x y
  | .except _ ps => (∀ e, x.1 e ⊢ₛ y.1 e) ∧ @entails ps x.2 y.2

scoped infix:25 " ⊢ₑ " => FailConds.entails

@[simp, refl]
theorem FailConds.entails.refl {ps : PostShape} (x : FailConds ps) : x ⊢ₑ x := by
  induction ps <;> simp [entails, *]

theorem FailConds.entails.rfl {ps : PostShape} {x : FailConds ps} : x ⊢ₑ x := refl x

theorem FailConds.entails.trans {ps : PostShape} {x y z : FailConds ps} : (x ⊢ₑ y) → (y ⊢ₑ z) → x ⊢ₑ z := by
  induction ps
  case pure => intro _ _; trivial
  case arg σ s ih => exact ih
  case except ε s ih => intro h₁ h₂; exact ⟨fun e => (h₁.1 e).trans (h₂.1 e), ih h₁.2 h₂.2⟩

@[simp]
theorem FailConds.entails_false {x : FailConds ps} : FailConds.false ⊢ₑ x := by
  induction ps <;> simp_all [false, const, entails, SPred.false_elim]

@[simp]
theorem FailConds.entails_true {x : FailConds ps} : x ⊢ₑ FailConds.true := by
  induction ps <;> simp_all [true, const, entails]

@[simp]
def FailConds.and {ps : PostShape.{u}} (x : FailConds ps) (y : FailConds ps) : FailConds ps :=
  match ps with
  | .pure => ⟨⟩
  | .arg _ ps => @FailConds.and ps x y
  | .except _ _ => (fun e => SPred.and (x.1 e) (y.1 e), FailConds.and x.2 y.2)

infixr:35 " ∧ₑ " => FailConds.and

theorem FailConds.and_true {x : FailConds ps} : x ∧ₑ FailConds.true ⊢ₑ x := by
  induction ps
  case pure => trivial
  case arg ih => exact ih
  case except ε ps ih =>
    simp_all only [true, and, const]
    constructor <;> simp only [SPred.and_true.mp, implies_true, ih]

theorem FailConds.true_and {x : FailConds ps} : FailConds.true ∧ₑ x ⊢ₑ x := by
  induction ps
  case pure => trivial
  case arg ih => exact ih
  case except ε ps ih =>
    simp_all only [true, and, const]
    constructor <;> simp only [SPred.true_and.mp, implies_true, ih]

theorem FailConds.and_false {x : FailConds ps} : x ∧ₑ FailConds.false ⊢ₑ FailConds.false := by
  induction ps
  case pure => trivial
  case arg ih => exact ih
  case except ε ps ih =>
    simp_all only [false, and, const]
    constructor <;> simp only [SPred.and_false.mp, implies_true, ih]

theorem FailConds.false_and {x : FailConds ps} : FailConds.false ∧ₑ x ⊢ₑ FailConds.false := by
  induction ps
  case pure => trivial
  case arg ih => exact ih
  case except ε ps ih =>
    simp_all only [and, false, const]
    constructor <;> simp only [SPred.false_and.mp, implies_true, ih]

theorem FailConds.and_eq_left {ps : PostShape} {p q : FailConds ps} (h : p ⊢ₑ q) :
    p = (p ∧ₑ q) := by
  induction ps
  case pure => trivial
  case arg ih => exact ih h
  case except ε ps ih =>
    simp_all only [and]
    apply Prod.ext
    · ext a; exact (SPred.and_eq_left.mp (h.1 a)).to_eq
    · exact ih h.2

/--
  A multi-barreled postcondition for the given predicate shape.
  ```
  example : PostCond α (.arg ρ .pure) = ((α → ρ → Prop) × Unit) := rfl
  example : PostCond α (.except ε .pure) = ((α → Prop) × (ε → Prop) × Unit) := rfl
  example : PostCond α (.arg σ (.except ε .pure)) = ((α → σ → Prop) × (ε → Prop) × Unit) := rfl
  example : PostCond α (.except ε (.arg σ .pure)) = ((α → σ → Prop) × (ε → σ → Prop) × Unit) := rfl
  ```
-/
abbrev PostCond (α : Type u) (ps : PostShape.{u}) : Type u :=
  (α → Assertion ps) × FailConds ps

@[inherit_doc PostCond]
scoped macro:max "post⟨" handlers:term,+,? "⟩" : term =>
  `(by exact ⟨$handlers,*, ()⟩)
  -- NB: Postponement through by exact is the entire point of this macro
  -- until https://github.com/leanprover/lean4/pull/8074 lands

/-- A postcondition expressing total correctness. -/
abbrev PostCond.total (p : α → Assertion ps) : PostCond α ps :=
  (p, FailConds.false)

@[inherit_doc PostCond.total]
scoped macro:max ppAllowUngrouped "⇓" xs:term:max+ " => " e:term : term =>
  `(PostCond.total (by exact fun $xs* => spred($e)))

/-- A postcondition expressing partial correctness. -/
abbrev PostCond.partial (p : α → Assertion ps) : PostCond α ps :=
  (p, FailConds.true)

instance : Inhabited (PostCond α ps) where
  default := PostCond.total fun _ => default

@[simp]
def PostCond.entails (p q : PostCond α ps) : Prop :=
  (∀ a, SPred.entails (p.1 a) (q.1 a)) ∧ FailConds.entails p.2 q.2

scoped infix:25 " ⊢ₚ " => PostCond.entails

@[refl,simp]
theorem PostCond.entails.refl (Q : PostCond α ps) : Q ⊢ₚ Q := ⟨fun a => SPred.entails.refl (Q.1 a), FailConds.entails.refl Q.2⟩
theorem PostCond.entails.rfl {Q : PostCond α ps} : Q ⊢ₚ Q := refl Q

theorem PostCond.entails.trans {P Q R : PostCond α ps} (h₁ : P ⊢ₚ Q) (h₂ : Q ⊢ₚ R) : P ⊢ₚ R :=
  ⟨fun a => (h₁.1 a).trans (h₂.1 a), h₁.2.trans h₂.2⟩

@[simp]
theorem PostCond.entails_total (p : α → Assertion ps) (q : PostCond α ps) : PostCond.total p ⊢ₚ q ↔ ∀ a, p a ⊢ₛ q.1 a := by
  simp only [entails, FailConds.entails_false, and_true]

@[simp]
theorem PostCond.entails_partial (p : PostCond α ps) (q : α → Assertion ps) : p ⊢ₚ PostCond.partial q ↔ ∀ a, p.1 a ⊢ₛ q a := by
  simp only [entails, FailConds.entails_true, and_true]

abbrev PostCond.and (p : PostCond α ps) (q : PostCond α ps) : PostCond α ps :=
  (fun a => SPred.and (p.1 a) (q.1 a), FailConds.and p.2 q.2)

scoped infixr:35 " ∧ₚ " => PostCond.and

theorem PostCond.and_eq_left {p q : PostCond α ps} (h : p ⊢ₚ q) :
    p = (p ∧ₚ q) := by
  ext
  · exact (SPred.and_eq_left.mp (h.1 _)).to_eq
  · exact FailConds.and_eq_left h.2
