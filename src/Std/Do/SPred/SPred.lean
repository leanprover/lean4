/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Init.Ext
public import Std.Do.SPred.SVal

@[expose] public section

set_option linter.missingDocs true

/-!
# State-indexed predicates

This module provides a type `SPred σs` of predicates indexed by a list of states.
This type forms the basis for the notion of assertion in `Std.Do`; see `Std.Do.Assertion`.
-/

namespace Std.Do

/--
A predicate over states, where each state is defined by a list of component state types.

Example:
```lean example
SPred [Nat, Bool] = (Nat → Bool → ULift Prop)
```
-/
abbrev SPred (σs : List (Type u)) : Type u := SVal σs (ULift Prop)

namespace SPred

universe u
variable {σs : List (Type u)}

@[ext]
theorem ext_nil {P Q : SPred []} (h : P.down ↔ Q.down) : P = Q := by
  cases P; cases Q; simp_all

@[ext]
theorem ext_cons {P Q : SPred (σ::σs)} : (∀ s, P s = Q s) → P = Q := funext

/--
A pure proposition `P : Prop` embedded into `SPred`.
Prefer to use notation `⌜P⌝`.
-/
def pure {σs : List (Type u)} (P : Prop) : SPred σs := match σs with
  | [] => ULift.up P
  | _ :: _ => fun _ => pure P
theorem pure_nil : pure (σs:=[]) P = ULift.up P := rfl
theorem pure_cons : pure (σs:=σ::σs) P = fun _ => pure P := rfl

/--
Entailment in `SPred`.

One predicate `P` entails another predicate `Q` if `Q` is true in every state in which `P` is true.
Unlike implication (`SPred.imp`), entailment is not itself an `SPred`, but is instead an ordinary
proposition.
-/
def entails {σs : List (Type u)} (P Q : SPred σs) : Prop := match σs with
  | [] => P.down → Q.down
  | σ :: _ => ∀ (s : σ), entails (P s) (Q s)
@[simp, grind =] theorem entails_nil {P Q : SPred []} : entails P Q = (P.down → Q.down) := rfl
-- We would like to make `entails_cons` @[simp], but that has no effect until we merge #9015.
-- Until then, we have `entails_<n>` for n ∈ [1:5] in DerivedLaws.lean.
theorem entails_cons {P Q : SPred (σ::σs)} : entails P Q = (∀ s, entails (P s) (Q s)) := rfl
theorem entails_cons_intro {P Q : SPred (σ::σs)} : (∀ s, entails (P s) (Q s)) → entails P Q := by simp only [entails_cons, imp_self]

-- Reducibility of entails must be semi-reducible so that entails_refl is useful for rfl

/--
Logical equivalence of `SPred`.

Logically equivalent predicates are equal. Use `SPred.bientails.to_eq` to convert bi-entailment to
equality.
-/
def bientails {σs : List (Type u)} (P Q : SPred σs) : Prop := match σs with
  | [] => P.down ↔ Q.down
  | σ :: _ => ∀ (s : σ), bientails (P s) (Q s)
@[simp, grind =] theorem bientails_nil {P Q : SPred []} : bientails P Q = (P.down ↔ Q.down) := rfl
theorem bientails_cons {P Q : SPred (σ::σs)} : bientails P Q = (∀ s, bientails (P s) (Q s)) := rfl
theorem bientails_cons_intro {P Q : SPred (σ::σs)} : (∀ s, bientails (P s) (Q s)) → bientails P Q := by simp only [bientails_cons, imp_self]

/-- Conjunction in `SPred`: states that satisfy `P` and satisfy `Q` satisfy `spred(P ∧ Q)`. -/
def and {σs : List (Type u)} (P Q : SPred σs) : SPred σs := match σs with
  | [] => ⟨P.down ∧ Q.down⟩
  | σ :: _ => fun (s : σ) => and (P s) (Q s)
@[simp, grind =] theorem and_nil {P Q : SPred []} : and P Q = ⟨P.down ∧ Q.down⟩ := rfl
@[simp, grind =] theorem and_cons {P Q : SPred (σ::σs)} : and P Q s = and (P s) (Q s) := rfl

/-- Disjunction in `SPred`: states that either satisfy `P` or satisfy `Q` satisfy `spred(P ∨ Q)`. -/
def or {σs : List (Type u)} (P Q : SPred σs) : SPred σs := match σs with
  | [] => ⟨P.down ∨ Q.down⟩
  | σ :: _ => fun (s : σ) => or (P s) (Q s)
@[simp, grind =] theorem or_nil {P Q : SPred []} : or P Q = ⟨P.down ∨ Q.down⟩ := rfl
@[simp, grind =] theorem or_cons {P Q : SPred (σ::σs)} : or P Q s = or (P s) (Q s) := rfl

/-- Negation in `SPred`: states that do not satisfy `P` satisfy `spred(¬ P)`. -/
def not {σs : List (Type u)} (P : SPred σs) : SPred σs := match σs with
  | [] => ⟨¬ P.down⟩
  | σ :: _ => fun (s : σ) => not (P s)
@[simp, grind =] theorem not_nil {P : SPred []} : not P = ⟨¬ P.down⟩ := rfl
@[simp, grind =] theorem not_cons {P : SPred (σ::σs)} : not P s = not (P s) := rfl

/--
Implication in `SPred`: states that satisfy `Q` whenever they satisfy `P` satisfy `spred(P → Q)`.
-/
def imp {σs : List (Type u)} (P Q : SPred σs) : SPred σs := match σs with
  | [] => ⟨P.down → Q.down⟩
  | σ :: _ => fun (s : σ) => imp (P s) (Q s)
@[simp, grind =] theorem imp_nil {P Q : SPred []} : imp P Q = ⟨P.down → Q.down⟩ := rfl
@[simp, grind =] theorem imp_cons {P Q : SPred (σ::σs)} : imp P Q s = imp (P s) (Q s) := rfl

/--
Biimplication in `SPred`: states that either satisfy both `P` and `Q` or satisfy neither satisfy
`spred(P ↔ Q)`.
-/
def iff {σs : List (Type u)} (P Q : SPred σs) : SPred σs := match σs with
  | [] => ⟨P.down ↔ Q.down⟩
  | σ :: _ => fun (s : σ) => iff (P s) (Q s)
@[simp, grind =] theorem iff_nil {P Q : SPred []} : iff P Q = ⟨P.down ↔ Q.down⟩ := rfl
@[simp, grind =] theorem iff_cons {P Q : SPred (σ::σs)} : iff P Q s = iff (P s) (Q s) := rfl

/-- Existential quantifier in `SPred`. -/
def «exists» {α : Sort u} {σs : List (Type v)} (P : α → SPred σs) : SPred σs := match σs with
  | [] => ⟨∃ a, (P a).down⟩
  | σ :: _ => fun (s : σ) => «exists» (fun a => P a s)
@[simp, grind =] theorem exists_nil {α} {P : α → SPred []} : «exists» P = ⟨∃ a, (P a).down⟩ := rfl
@[simp] theorem exists_cons {α} {P : α → SPred (σ::σs)} : «exists» P s = «exists» (fun a => P a s) := rfl

/-- Universal quantifier in `SPred`. -/
def «forall» {α : Sort u} {σs : List (Type v)} (P : α → SPred σs) : SPred σs := match σs with
  | [] => ⟨∀ a, (P a).down⟩
  | σ :: _ => fun (s : σ) => «forall» (fun a => P a s)
@[simp, grind =] theorem forall_nil {α} {P : α → SPred []} : «forall» P = ⟨∀ a, (P a).down⟩ := rfl
@[simp, grind =] theorem forall_cons {α} {P : α → SPred (σ::σs)} : «forall» P s = «forall» (fun a => P a s) := rfl

/--
Conjunction of a list of stateful predicates. A state satisfies `conjunction env` if it satisfies
all predicates in `env`.
-/
def conjunction {σs : List (Type u)} (env : List (SPred σs)) : SPred σs := match env with
  | [] => pure True
  | P::env => P.and (conjunction env)
@[simp, grind =] theorem conjunction_nil : conjunction ([] : List (SPred σs)) = pure True := rfl
@[simp, grind =] theorem conjunction_cons {P : SPred σs} {env : List (SPred σs)} : conjunction (P::env) = P.and (conjunction env) := rfl
@[simp, grind =] theorem conjunction_apply {env : List (SPred (σ::σs))} : conjunction env s = conjunction (env.map (· s)) := by
  induction env <;> simp [conjunction, pure_cons, *]
