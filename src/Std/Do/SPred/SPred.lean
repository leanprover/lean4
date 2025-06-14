/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
prelude
import Init.Ext
import Std.Do.SPred.SVal

/-!
# State-indexed predicates

This module provides a type `SPred σs` of predicates indexed by a list of states.
This type forms the basis for the notion of assertion in `Std.Do`; see `Std.Do.Assertion`.
-/

namespace Std.Do

/--
  A predicate indexed by a list of states.
  ```
  example : SPred [Nat, Bool] = (Nat → Bool → Prop) := rfl
  ```
-/
abbrev SPred (σs : List Type) : Type := SVal σs Prop

namespace SPred

/-- A pure proposition `P : Prop` embedded into `SPred`. For internal use in this module only; prefer to use idiom bracket notation `⌜P⌝. -/
private abbrev pure {σs : List Type} (P : Prop) : SPred σs := SVal.curry (fun _ => P)

@[ext]
theorem ext {σs : List Type} {P Q : SPred (σ::σs)} : (∀ s, P s = Q s) → P = Q := funext

/-- Entailment in `SPred`. -/
def entails {σs : List Type} (P Q : SPred σs) : Prop := match σs with
| [] => P → Q
| σ :: _ => ∀ (s : σ), entails (P s) (Q s)
@[simp] theorem entails_nil {P Q : SPred []} : entails P Q = (P → Q) := rfl
theorem entails_cons {σs : List Type} {P Q : SPred (σ::σs)} : entails P Q = (∀ s, entails (P s) (Q s)) := rfl
theorem entails_cons_intro {σs : List Type} {P Q : SPred (σ::σs)} : (∀ s, entails (P s) (Q s)) → entails P Q := by simp only [entails, imp_self]

-- Reducibility of entails must be semi-reducible so that entails_refl is useful for rfl

/-- Equivalence relation on `SPred`. Convert to `Eq` via `bientails.to_eq`. -/
def bientails {σs : List Type} (P Q : SPred σs) : Prop := match σs with
| [] => P ↔ Q
| σ :: _ => ∀ (s : σ), bientails (P s) (Q s)
@[simp] theorem bientails_nil {P Q : SPred []} : bientails P Q = (P ↔ Q) := rfl
theorem bientails_cons {σs : List Type} {P Q : SPred (σ::σs)} : bientails P Q = (∀ s, bientails (P s) (Q s)) := rfl
theorem bientails_cons_intro {σs : List Type} {P Q : SPred (σ::σs)} : (∀ s, bientails (P s) (Q s)) → bientails P Q := by simp only [bientails, imp_self]

/-- Conjunction in `SPred`. -/
def and {σs : List Type} (P Q : SPred σs) : SPred σs := match σs with
| [] => P ∧ Q
| σ :: _ => fun (s : σ) => and (P s) (Q s)
@[simp] theorem and_nil {P Q : SPred []} : and P Q = (P ∧ Q) := rfl
@[simp] theorem and_cons {σs : List Type} {P Q : SPred (σ::σs)} : and P Q s = and (P s) (Q s) := rfl

/-- Disjunction in `SPred`. -/
def or {σs : List Type} (P Q : SPred σs) : SPred σs := match σs with
| [] => P ∨ Q
| σ :: _ => fun (s : σ) => or (P s) (Q s)
@[simp] theorem or_nil {P Q : SPred []} : or P Q = (P ∨ Q) := rfl
@[simp] theorem or_cons {σs : List Type} {P Q : SPred (σ::σs)} : or P Q s = or (P s) (Q s) := rfl

/-- Negation in `SPred`. -/
def not {σs : List Type} (P : SPred σs) : SPred σs := match σs with
| [] => ¬ P
| σ :: _ => fun (s : σ) => not (P s)
@[simp] theorem not_nil {P : SPred []} : not P = (¬ P) := rfl
@[simp] theorem not_cons {σs : List Type} {P : SPred (σ::σs)} : not P s = not (P s) := rfl

/-- Implication in `SPred`. -/
def imp {σs : List Type} (P Q : SPred σs) : SPred σs := match σs with
| [] => P → Q
| σ :: _ => fun (s : σ) => imp (P s) (Q s)
@[simp] theorem imp_nil {P Q : SPred []} : imp P Q = (P → Q) := rfl
@[simp] theorem imp_cons {σs : List Type} {P Q : SPred (σ::σs)} : imp P Q s = imp (P s) (Q s) := rfl

/-- Biconditional in `SPred`. -/
def iff {σs : List Type} (P Q : SPred σs) : SPred σs := match σs with
| [] => P ↔ Q
| σ :: _ => fun (s : σ) => iff (P s) (Q s)
@[simp] theorem iff_nil {P Q : SPred []} : iff P Q = (P ↔ Q) := rfl
@[simp] theorem iff_cons {σs : List Type} {P Q : SPred (σ::σs)} : iff P Q s = iff (P s) (Q s) := rfl

/-- Existential quantifier in `SPred`. -/
def «exists» {α} {σs : List Type} (P : α → SPred σs) : SPred σs := match σs with
| [] => ∃ a, P a
| σ :: _ => fun (s : σ) => «exists» (fun a => P a s)
@[simp] theorem exists_nil {α} {P : α → SPred []} : «exists» P = (∃ a, P a) := rfl
@[simp] theorem exists_cons {σs : List Type} {α} {P : α → SPred (σ::σs)} : «exists» P s = «exists» (fun a => P a s) := rfl

/-- Universal quantifier in `SPred`. -/
def «forall» {α} {σs : List Type} (P : α → SPred σs) : SPred σs := match σs with
| [] => ∀ a, P a
| σ :: _ => fun (s : σ) => «forall» (fun a => P a s)
@[simp] theorem forall_nil {α} {P : α → SPred []} : «forall» P = (∀ a, P a) := rfl
@[simp] theorem forall_cons {σs : List Type} {α} {P : α → SPred (σ::σs)} : «forall» P s = «forall» (fun a => P a s) := rfl

/-- Conjunction of a list of `SPred`. -/
def conjunction {σs : List Type} (env : List (SPred σs)) : SPred σs := match env with
| [] => pure True
| P::env => P.and (conjunction env)
@[simp] theorem conjunction_nil {σs : List Type} : conjunction ([] : List (SPred σs)) = pure True := rfl
@[simp] theorem conjunction_cons {σs : List Type} {P : SPred σs} {env : List (SPred σs)} : conjunction (P::env) = P.and (conjunction env) := rfl
@[simp] theorem conjunction_apply {σs : List Type} {env : List (SPred (σ::σs))} : conjunction env s = conjunction (env.map (· s)) := by
  induction env <;> simp [conjunction, *]
