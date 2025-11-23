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
  example : ExceptConds (.pure) = Unit := rfl
  example : ExceptConds (.except ε .pure) = ((ε → ULift Prop) × Unit) := rfl
  example : ExceptConds (.arg σ (.except ε .pure)) = ((ε → ULift Prop) × Unit) := rfl
  example : ExceptConds (.except ε (.arg σ .pure)) = ((ε → σ → ULift Prop) × Unit) := rfl
  ```
-/
def ExceptConds : PostShape.{u} → Type u
  | .pure => PUnit
  | .arg _ ps => ExceptConds ps
  | .except ε ps => (ε → Assertion ps) × ExceptConds ps

def ExceptConds.const {ps : PostShape.{u}} (p : Prop) : ExceptConds ps := match ps with
  | .pure => ⟨⟩
  | .arg _ ps => @ExceptConds.const ps p
  | .except _ ps => (fun _ε => spred(⌜p⌝), @ExceptConds.const ps p)

def ExceptConds.true : ExceptConds ps := ExceptConds.const True
def ExceptConds.false : ExceptConds ps := ExceptConds.const False

@[simp, grind =]
theorem ExceptConds.fst_const {ps : PostShape.{u}} (p : Prop) :
    Prod.fst (ExceptConds.const p (ps := .except ε ps)) = fun _ε => ⌜p⌝ := rfl

@[simp, grind =]
theorem ExceptConds.snd_const {ps : PostShape.{u}} (p : Prop) :
    Prod.snd (ExceptConds.const p (ps := .except ε ps)) = ExceptConds.const p := rfl

@[simp, grind =]
theorem ExceptConds.fst_true {ps : PostShape.{u}} :
    Prod.fst (ExceptConds.true (ps := .except ε ps)) = fun _ε => ⌜True⌝ := rfl

@[simp, grind =]
theorem ExceptConds.snd_true {ps : PostShape.{u}} :
    Prod.snd (ExceptConds.true (ps := .except ε ps)) = ExceptConds.true := rfl

@[simp, grind =]
theorem ExceptConds.fst_false {ps : PostShape.{u}} :
    Prod.fst (ExceptConds.false (ps := .except ε ps)) = fun _ε => ⌜False⌝ := rfl

@[simp, grind =]
theorem ExceptConds.snd_false {ps : PostShape.{u}} :
    Prod.snd (ExceptConds.false (ps := .except ε ps)) = ExceptConds.false := rfl

instance : Inhabited (ExceptConds ps) where
  default := ExceptConds.true

def ExceptConds.entails {ps : PostShape.{u}} (x y : ExceptConds ps) : Prop :=
  match ps with
  | .pure => True
  | .arg _ ps => @entails ps x y
  | .except _ ps => (∀ e, x.1 e ⊢ₛ y.1 e) ∧ @entails ps x.2 y.2

scoped infixr:25 " ⊢ₑ " => ExceptConds.entails

@[refl, simp]
theorem ExceptConds.entails.refl {ps : PostShape} (x : ExceptConds ps) : x ⊢ₑ x := by
  induction ps <;> simp [entails, *]

theorem ExceptConds.entails.rfl {ps : PostShape} {x : ExceptConds ps} : x ⊢ₑ x := refl x

theorem ExceptConds.entails.trans {ps : PostShape} {x y z : ExceptConds ps} : (x ⊢ₑ y) → (y ⊢ₑ z) → x ⊢ₑ z := by
  induction ps
  case pure => intro _ _; trivial
  case arg σ s ih => exact ih
  case except ε s ih => intro h₁ h₂; exact ⟨fun e => (h₁.1 e).trans (h₂.1 e), ih h₁.2 h₂.2⟩

@[simp]
theorem ExceptConds.entails_false {x : ExceptConds ps} : ExceptConds.false ⊢ₑ x := by
  induction ps <;> simp_all [false, const, entails, SPred.false_elim]

@[simp]
theorem ExceptConds.entails_true {x : ExceptConds ps} : x ⊢ₑ ExceptConds.true := by
  induction ps <;> simp_all [true, const, entails]

def ExceptConds.and {ps : PostShape.{u}} (x : ExceptConds ps) (y : ExceptConds ps) : ExceptConds ps :=
  match ps with
  | .pure => ⟨⟩
  | .arg _ ps => @ExceptConds.and ps x y
  | .except _ _ => (fun e => SPred.and (x.1 e) (y.1 e), ExceptConds.and x.2 y.2)

infixr:35 " ∧ₑ " => ExceptConds.and

@[simp]
theorem ExceptConds.fst_and {x₁ x₂ : ExceptConds (.except ε ps)} : (x₁ ∧ₑ x₂).fst = fun e => spred(x₁.fst e ∧ x₂.fst e) := rfl

@[simp]
theorem ExceptConds.snd_and {x₁ x₂ : ExceptConds (.except ε ps)} : (x₁ ∧ₑ x₂).snd = (x₁.snd ∧ₑ x₂.snd) := rfl

@[simp]
theorem ExceptConds.and_true {x : ExceptConds ps} : x ∧ₑ ExceptConds.true ⊢ₑ x := by
  induction ps
  case pure => trivial
  case arg ih => exact ih
  case except ε ps ih =>
    simp_all only [true, and, const]
    constructor <;> simp only [SPred.and_true.mp, implies_true, ih]

@[simp]
theorem ExceptConds.true_and {x : ExceptConds ps} : ExceptConds.true ∧ₑ x ⊢ₑ x := by
  induction ps
  case pure => trivial
  case arg ih => exact ih
  case except ε ps ih =>
    simp_all only [true, and, const]
    constructor <;> simp only [SPred.true_and.mp, implies_true, ih]

@[simp]
theorem ExceptConds.and_false {x : ExceptConds ps} : x ∧ₑ ExceptConds.false ⊢ₑ ExceptConds.false := by
  induction ps
  case pure => trivial
  case arg ih => exact ih
  case except ε ps ih =>
    simp_all only [false, and, const]
    constructor <;> simp only [SPred.and_false.mp, implies_true, ih]

@[simp]
theorem ExceptConds.false_and {x : ExceptConds ps} : ExceptConds.false ∧ₑ x ⊢ₑ ExceptConds.false := by
  induction ps
  case pure => trivial
  case arg ih => exact ih
  case except ε ps ih =>
    simp_all only [and, false, const]
    constructor <;> simp only [SPred.false_and.mp, implies_true, ih]

theorem ExceptConds.and_eq_left {ps : PostShape} {p q : ExceptConds ps} (h : p ⊢ₑ q) :
    p = (p ∧ₑ q) := by
  induction ps
  case pure => trivial
  case arg ih => exact ih h
  case except ε ps ih =>
    simp_all only [and]
    apply Prod.ext
    · ext a; exact (SPred.and_eq_left.mp (h.1 a)).to_eq
    · exact ih h.2

def ExceptConds.imp {ps : PostShape.{u}} (x : ExceptConds ps) (y : ExceptConds ps) : ExceptConds ps :=
  match ps with
  | .pure => ⟨⟩
  | .arg _ ps => @ExceptConds.imp ps x y
  | .except _ _ => (fun e => SPred.imp (x.1 e) (y.1 e), ExceptConds.imp x.2 y.2)

infixr:25 " →ₑ " => ExceptConds.imp

@[simp]
theorem ExceptConds.fst_imp {x₁ x₂ : ExceptConds (.except ε ps)} : (x₁ →ₑ x₂).fst = fun e => spred(x₁.fst e → x₂.fst e) := rfl

@[simp]
theorem ExceptConds.snd_imp {x₁ x₂ : ExceptConds (.except ε ps)} : (x₁ →ₑ x₂).snd = (x₁.snd →ₑ x₂.snd) := rfl

theorem ExceptConds.imp_intro {P Q R : ExceptConds ps} (h : P ∧ₑ Q ⊢ₑ R) : P ⊢ₑ Q →ₑ R := by
  induction ps
  case pure => trivial
  case arg ih => exact ih h
  case except ε ps ih => simp_all [entails, SPred.imp_intro]

theorem ExceptConds.imp_elim {P Q R : ExceptConds ps} (h : P ⊢ₑ (Q →ₑ R)) : P ∧ₑ Q ⊢ₑ R := by
  induction ps
  case pure => trivial
  case arg ih => exact ih h
  case except ε ps ih => simp_all [entails, SPred.imp_elim]

@[simp]
theorem ExceptConds.true_imp {x : ExceptConds ps} : (ExceptConds.true →ₑ x) = x := by
  induction ps
  case pure => trivial
  case arg ih => exact ih
  case except ε ps ih =>
    cases x
    simp only [ih, imp, fst_true, snd_true, SPred.true_imp.to_eq]

@[simp]
theorem ExceptConds.false_imp {x : ExceptConds ps} : (ExceptConds.false →ₑ x) = ExceptConds.true := by
  induction ps
  case pure => trivial
  case arg ih => exact ih
  case except ε ps ih =>
    simp only [true, const, ih, imp, fst_false, snd_false, SPred.false_imp.to_eq]

theorem ExceptConds.and_imp {x₁ x₂ : ExceptConds ps} : (x₁ ∧ₑ (x₁ →ₑ x₂)) ⊢ₑ x₁ ∧ₑ x₂ := by
  induction ps
  case pure => trivial
  case arg ih => exact ih
  case except ε ps ih => simp_all [and, imp, entails, SPred.and_imp]

/--
A postcondition for the given predicate shape, with one `Assertion` for the terminating case and
one `Assertion` for each `.except` layer in the predicate shape.
```
variable (α σ ε : Type)
example : PostCond α (.arg σ .pure) = ((α → σ → ULift Prop) × PUnit) := rfl
example : PostCond α (.except ε .pure) = ((α → ULift Prop) × (ε → ULift Prop) × PUnit) := rfl
example : PostCond α (.arg σ (.except ε .pure)) = ((α → σ → ULift Prop) × (ε → ULift Prop) × PUnit) := rfl
example : PostCond α (.except ε (.arg σ .pure)) = ((α → σ → ULift Prop) × (ε → σ → ULift Prop) × PUnit) := rfl
```
-/
abbrev PostCond (α : Type u) (ps : PostShape.{u}) : Type u :=
  (α → Assertion ps) × ExceptConds ps

@[inherit_doc PostCond]
scoped macro:max "post⟨" handlers:term,+,? "⟩" : term =>
  `(by exact ⟨$handlers,*, ()⟩)
  -- NB: Postponement through by exact is the entire point of this macro
  -- until https://github.com/leanprover/lean4/pull/8074 lands

/--
A postcondition expressing total correctness.
That is, it expresses that the asserted computation finishes without throwing an exception
*and* the result satisfies the given predicate `p`.
-/
abbrev PostCond.noThrow (p : α → Assertion ps) : PostCond α ps :=
  (p, ExceptConds.false)

@[inherit_doc PostCond.noThrow]
scoped macro:max ppAllowUngrouped "⇓" xs:term:max+ " => " e:term : term =>
  `(PostCond.noThrow (by exact fun $xs* => spred($e)))

/--
A postcondition expressing partial correctness.
That is, it expresses that *if* the asserted computation finishes without throwing an exception
*then* the result satisfies the given predicate `p`.
Nothing is asserted when the computation throws an exception.
-/
abbrev PostCond.mayThrow (p : α → Assertion ps) : PostCond α ps :=
  (p, ExceptConds.true)

@[inherit_doc PostCond.mayThrow]
scoped macro:max ppAllowUngrouped "⇓?" xs:term:max+ " => " e:term : term =>
  `(PostCond.mayThrow (by exact fun $xs* => spred($e)))

instance : Inhabited (PostCond α ps) where
  default := PostCond.noThrow fun _ => default

@[simp]
def PostCond.entails (p q : PostCond α ps) : Prop :=
  (∀ a, SPred.entails (p.1 a) (q.1 a)) ∧ ExceptConds.entails p.2 q.2

scoped infixr:25 " ⊢ₚ " => PostCond.entails

@[refl, simp]
theorem PostCond.entails.refl (Q : PostCond α ps) : Q ⊢ₚ Q := ⟨fun a => SPred.entails.refl (Q.1 a), ExceptConds.entails.refl Q.2⟩
theorem PostCond.entails.rfl {Q : PostCond α ps} : Q ⊢ₚ Q := refl Q

theorem PostCond.entails.trans {P Q R : PostCond α ps} (h₁ : P ⊢ₚ Q) (h₂ : Q ⊢ₚ R) : P ⊢ₚ R :=
  ⟨fun a => (h₁.1 a).trans (h₂.1 a), h₁.2.trans h₂.2⟩

@[simp]
theorem PostCond.entails_noThrow (p : α → Assertion ps) (q : PostCond α ps) : PostCond.noThrow p ⊢ₚ q ↔ ∀ a, p a ⊢ₛ q.1 a := by
  simp only [entails, ExceptConds.entails_false, and_true]

@[simp]
theorem PostCond.entails_mayThrow (p : PostCond α ps) (q : α → Assertion ps) : p ⊢ₚ PostCond.mayThrow q ↔ ∀ a, p.1 a ⊢ₛ q a := by
  simp only [entails, ExceptConds.entails_true, and_true]

abbrev PostCond.and (p : PostCond α ps) (q : PostCond α ps) : PostCond α ps :=
  (fun a => SPred.and (p.1 a) (q.1 a), ExceptConds.and p.2 q.2)

scoped infixr:35 " ∧ₚ " => PostCond.and

abbrev PostCond.imp (p : PostCond α ps) (q : PostCond α ps) : PostCond α ps :=
  (fun a => SPred.imp (p.1 a) (q.1 a), ExceptConds.imp p.2 q.2)

scoped infixr:25 " →ₚ " => PostCond.imp

theorem PostCond.and_imp : P' ∧ₚ (P' →ₚ Q') ⊢ₚ P' ∧ₚ Q' := by
  simp [SPred.and_imp, ExceptConds.and_imp]

theorem PostCond.and_left_of_entails {p q : PostCond α ps} (h : p ⊢ₚ q) :
    p = (p ∧ₚ q) := by
  ext
  · exact (SPred.and_eq_left.mp (h.1 _)).to_eq
  · exact ExceptConds.and_eq_left h.2
