/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune, Henrik Böving
-/
prelude
import Init.NotationExtra

namespace Std
namespace Sat

/--
For variables of type `α` and formulas of type `β`, `HSat.eval a f` is meant to determine whether
a formula `f` is true under assignment `a`.
-/
class HSat (α : Type u) (β : Type v) :=
  eval : (α → Bool) → β → Prop

/--
`a ⊨ f` reads formula `f` is true under assignment `a`.
-/
scoped infix:25 " ⊨ " => HSat.eval

/--
`a ⊭ f` reads formula `f` is false under assignment `a`.
-/
scoped notation:25 p:25 " ⊭ " f:30 => ¬(HSat.eval p f)

/--
`f` is not true under any assignment.
-/
def Unsatisfiable (α : Type u) {σ : Type v} [HSat α σ] (f : σ) : Prop :=
  ∀ (p : α → Bool), p ⊭ f

/-- `f1` and `f2` are logically equivalent -/
def liff (α : Type u) {σ1 : Type v} {σ2 : Type w} [HSat α σ1] [HSat α σ2] (f1 : σ1) (f2 : σ2)
    : Prop :=
  ∀ (p : α → Bool), p ⊨ f1 ↔ p ⊨ f2

/-- `f1` logically implies `f2` -/
def limplies (α : Type u) {σ1 : Type v} {σ2 : Type w} [HSat α σ1] [HSat α σ2] (f1 : σ1) (f2 : σ2)
    : Prop :=
  ∀ (p : α → Bool), p ⊨ f1 → p ⊨ f2

/-- `f1` is unsat iff `f2` is unsat -/
def equisat (α : Type u) {σ1 : Type v} {σ2 : Type w} [HSat α σ1] [HSat α σ2] (f1 : σ1) (f2 : σ2)
    : Prop :=
  unsatisfiable α f1 ↔ unsatisfiable α f2

/--
For any given assignment `f1` or `f2` is not true.
-/
def incompatible (α : Type u) {σ1 : Type v} {σ2 : Type w} [HSat α σ1] [HSat α σ2] (f1 : σ1)
    (f2 : σ2) : Prop :=
  ∀ (p : α → Bool), (p ⊭ f1) ∨ (p ⊭ f2)

protected theorem liff.refl {α : Type u} {σ : Type v} [HSat α σ] (f : σ) : liff α f f :=
  (fun _ => Iff.rfl)

protected theorem liff.symm {α : Type u} {σ1 : Type v} {σ2 : Type 2} [HSat α σ1] [HSat α σ2]
    (f1 : σ1) (f2 : σ2) :
    liff α f1 f2 → liff α f2 f1 := by
  intros h p
  rw [h p]

protected theorem liff.trans {α : Type u} {σ1 : Type v} {σ2 : Type w} {σ3 : Type x} [HSat α σ1]
    [HSat α σ2] [HSat α σ3] (f1 : σ1) (f2 : σ2) (f3 : σ3)
    : liff α f1 f2 → liff α f2 f3 → liff α f1 f3 := by
  intros f1_eq_f2 f2_eq_f3 p
  rw [f1_eq_f2 p, f2_eq_f3 p]

protected theorem limplies.refl {α : Type u} {σ : Type v} [HSat α σ] (f : σ) : limplies α f f :=
  (fun _ => id)

protected theorem limplies.trans {α : Type u} {σ1 : Type v} {σ2 : Type w} {σ3 : Type x} [HSat α σ1]
    [HSat α σ2] [HSat α σ3] (f1 : σ1) (f2 : σ2) (f3 : σ3)
    : limplies α f1 f2 → limplies α f2 f3 → limplies α f1 f3 := by
  intros f1_implies_f2 f2_implies_f3 p p_entails_f1
  exact f2_implies_f3 p <| f1_implies_f2 p p_entails_f1

theorem liff_iff_limplies_and_limplies {α : Type u} {σ1 : Type v} {σ2 : Type w} [HSat α σ1]
    [HSat α σ2] (f1 : σ1) (f2 : σ2)
    : liff α f1 f2 ↔ limplies α f1 f2 ∧ limplies α f2 f1 := by
  constructor
  . intro h
    constructor
    . intro p
      rw [h p]
      exact id
    . intro p
      rw [h p]
      exact id
  . intros h p
    constructor
    . exact h.1 p
    . exact h.2 p

theorem liff_unsat {α : Type u} {σ1 : Type v} {σ2 : Type w} [HSat α σ1] [HSat α σ2] (f1 : σ1)
    (f2 : σ2) (h : liff α f1 f2)
    : unsatisfiable α f1 ↔ unsatisfiable α f2 := by
  constructor
  . intros f1_unsat p p_entails_f2
    rw [← h p] at p_entails_f2
    exact f1_unsat p p_entails_f2
  . intros f2_unsat p p_entails_f1
    rw [h p] at p_entails_f1
    exact f2_unsat p p_entails_f1

theorem limplies_unsat {α : Type u} {σ1 : Type v} {σ2 : Type w} [HSat α σ1] [HSat α σ2] (f1 : σ1)
    (f2 : σ2) (h : limplies α f2 f1)
    : unsatisfiable α f1 → unsatisfiable α f2 := by
  intros f1_unsat p p_entails_f2
  exact f1_unsat p <| h p p_entails_f2

theorem incompatible_of_unsat (α : Type u) {σ1 : Type v} {σ2 : Type w} [HSat α σ1] [HSat α σ2]
    (f1 : σ1) (f2 : σ2)
    : unsatisfiable α f1 → incompatible α f1 f2 := by
  intro h p
  exact Or.inl <| h p

theorem unsat_of_limplies_and_incompatible (α : Type u) {σ1 : Type v} {σ2 : Type w} [HSat α σ1]
    [HSat α σ2] (f1 : σ1) (f2 : σ2)
    : limplies α f1 f2 → incompatible α f1 f2 → unsatisfiable α f1 := by
  intro h1 h2 p pf1
  cases h2 p
  . next h2 =>
    exact h2 pf1
  . next h2 =>
    exact h2 <| h1 p pf1

protected theorem incompatible.symm {α : Type u} {σ1 : Type v} {σ2 : Type w} [HSat α σ1] [HSat α σ2]
    (f1 : σ1) (f2 : σ2)
    : incompatible α f1 f2 ↔ incompatible α f2 f1 := by
  constructor
  . intro h p
    exact Or.symm <| h p
  . intro h p
    exact Or.symm <| h p

end Sat
end Std
