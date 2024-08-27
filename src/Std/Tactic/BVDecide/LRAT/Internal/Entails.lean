/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune, Henrik Böving
-/
prelude
import Init.NotationExtra
import Init.PropLemmas

namespace Std.Tactic.BVDecide
namespace LRAT
namespace Internal

/--
For variables of type `α` and formulas of type `β`, `Entails.eval a f` is meant to determine whether
a formula `f` is true under assignment `a`.
-/
class Entails (α : Type u) (β : Type v) where
  eval : (α → Bool) → β → Prop

/--
`a ⊨ f` reads formula `f` is true under assignment `a`.
-/
scoped infix:25 " ⊨ " => Entails.eval

/--
`a ⊭ f` reads formula `f` is false under assignment `a`.
-/
scoped notation:25 a:25 " ⊭ " f:30 => ¬(Entails.eval a f)

/--
`f` is not true under any assignment.
-/
def Unsatisfiable (α : Type u) {σ : Type v} [Entails α σ] (f : σ) : Prop :=
  ∀ (a : α → Bool), a ⊭ f

/-- `f1` and `f2` are logically equivalent -/
def Liff (α : Type u) {σ1 : Type v} {σ2 : Type w} [Entails α σ1] [Entails α σ2] (f1 : σ1)
    (f2 : σ2) : Prop :=
  ∀ (a : α → Bool), a ⊨ f1 ↔ a ⊨ f2

/-- `f1` logically implies `f2` -/
def Limplies (α : Type u) {σ1 : Type v} {σ2 : Type w} [Entails α σ1] [Entails α σ2] (f1 : σ1)
    (f2 : σ2) : Prop :=
  ∀ (a : α → Bool), a ⊨ f1 → a ⊨ f2

/-- `f1` is unsat iff `f2` is unsat -/
def Equisat (α : Type u) {σ1 : Type v} {σ2 : Type w} [Entails α σ1] [Entails α σ2] (f1 : σ1)
    (f2 : σ2) : Prop :=
  Unsatisfiable α f1 ↔ Unsatisfiable α f2

/--
For any given assignment `f1` or `f2` is not true.
-/
def Incompatible (α : Type u) {σ1 : Type v} {σ2 : Type w} [Entails α σ1] [Entails α σ2] (f1 : σ1)
    (f2 : σ2) : Prop :=
  ∀ (a : α → Bool), (a ⊭ f1) ∨ (a ⊭ f2)

protected theorem Liff.refl {α : Type u} {σ : Type v} [Entails α σ] (f : σ) : Liff α f f :=
  (fun _ => Iff.rfl)

protected theorem Liff.symm {α : Type u} {σ1 : Type v} {σ2 : Type 2} [Entails α σ1] [Entails α σ2]
    (f1 : σ1) (f2 : σ2) :
    Liff α f1 f2 → Liff α f2 f1 := by
  intros h p
  rw [h p]

protected theorem Liff.trans {α : Type u} {σ1 : Type v} {σ2 : Type w} {σ3 : Type x} [Entails α σ1]
    [Entails α σ2] [Entails α σ3] (f1 : σ1) (f2 : σ2) (f3 : σ3) :
    Liff α f1 f2 → Liff α f2 f3 → Liff α f1 f3 := by
  intros f1_eq_f2 f2_eq_f3 a
  rw [f1_eq_f2 a, f2_eq_f3 a]

protected theorem Limplies.refl {α : Type u} {σ : Type v} [Entails α σ] (f : σ) : Limplies α f f :=
  (fun _ => id)

protected theorem Limplies.trans {α : Type u} {σ1 : Type v} {σ2 : Type w} {σ3 : Type x}
    [Entails α σ1] [Entails α σ2] [Entails α σ3] (f1 : σ1) (f2 : σ2) (f3 : σ3) :
    Limplies α f1 f2 → Limplies α f2 f3 → Limplies α f1 f3 := by
  intros f1_implies_f2 f2_implies_f3 a a_entails_f1
  exact f2_implies_f3 a <| f1_implies_f2 a a_entails_f1

theorem liff_iff_limplies_and_limplies {α : Type u} {σ1 : Type v} {σ2 : Type w} [Entails α σ1]
    [Entails α σ2] (f1 : σ1) (f2 : σ2) :
    Liff α f1 f2 ↔ Limplies α f1 f2 ∧ Limplies α f2 f1 := by
  simp [Liff, Limplies, iff_iff_implies_and_implies, forall_and]

theorem liff_unsat {α : Type u} {σ1 : Type v} {σ2 : Type w} [Entails α σ1] [Entails α σ2] (f1 : σ1)
    (f2 : σ2) (h : Liff α f1 f2) :
    Unsatisfiable α f1 ↔ Unsatisfiable α f2 := by
  simp only [Liff] at h
  simp [Unsatisfiable, h]

theorem limplies_unsat {α : Type u} {σ1 : Type v} {σ2 : Type w} [Entails α σ1] [Entails α σ2]
    (f1 : σ1) (f2 : σ2) (h : Limplies α f2 f1) :
    Unsatisfiable α f1 → Unsatisfiable α f2 := by
  intros f1_unsat a a_entails_f2
  exact f1_unsat a <| h a a_entails_f2

theorem incompatible_of_unsat (α : Type u) {σ1 : Type v} {σ2 : Type w} [Entails α σ1] [Entails α σ2]
    (f1 : σ1) (f2 : σ2) :
    Unsatisfiable α f1 → Incompatible α f1 f2 := by
  intro h a
  exact Or.inl <| h a

theorem unsat_of_limplies_and_incompatible (α : Type u) {σ1 : Type v} {σ2 : Type w} [Entails α σ1]
    [Entails α σ2] (f1 : σ1) (f2 : σ2) :
    Limplies α f1 f2 → Incompatible α f1 f2 → Unsatisfiable α f1 := by
  intro h1 h2 a af1
  cases h2 a
  · next h2 =>
    exact h2 af1
  · next h2 =>
    exact h2 <| h1 a af1

protected theorem Incompatible.symm {α : Type u} {σ1 : Type v} {σ2 : Type w} [Entails α σ1]
    [Entails α σ2] (f1 : σ1) (f2 : σ2) :
    Incompatible α f1 f2 ↔ Incompatible α f2 f1 := by
  constructor
  · intro h a
    exact Or.symm <| h a
  · intro h a
    exact Or.symm <| h a

end Internal
end LRAT
end Std.Tactic.BVDecide
