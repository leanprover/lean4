/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Henrik Böving
-/
module

prelude
public import Std.Sat.CNF.Basic
import Init.ByCases

public section

/-!
The semantics of `Clause` and `CNF`: evaluation with respect to an assignment, together with the
`Sat` and `Unsat` predicates built on top of it.
-/

namespace Std
namespace Sat

namespace CNF

namespace Clause

/--
Evaluating a `Clause` with respect to an assignment `a`.
-/
def eval (a : α → Bool) (c : Clause α) : Bool := c.literals.any fun (i, n) => a i == n

@[simp] theorem eval_empty (a : α → Bool) : Clause.eval a .empty = false := by
  simp [eval]

@[simp] theorem eval_add (a : α → Bool) :
    Clause.eval a (c.add atom pol) = (a atom == pol || Clause.eval a c) := by
  simp [eval, Bool.or_comm]

@[simp]
theorem eval_append (a : α → Bool) {c1 c2 : Clause α} :
    Clause.eval a (c1 ++ c2) = (Clause.eval a c1 || Clause.eval a c2) := by
  simp [eval]

theorem eval_congr (a1 a2 : α → Bool) (c : Clause α) (hw : ∀ i, VarMem i c → a1 i = a2 i) :
    eval a1 c = eval a2 c := by
  induction c using inductionOn with
  | empty => simp
  | add c atom pol ih =>
    simp
    rw [ih, hw]
    · simp
    · intro i hm
      apply hw
      simp [hm]

def Sat (a : α → Bool) (c : Clause α) : Prop := eval a c = true
def Unsat (c : Clause α) : Prop := ∀ a, eval a c = false

theorem sat_def (a : α → Bool) (c : Clause α) : Sat a c ↔ (eval a c = true) := by rfl
theorem unsat_def (c : Clause α) : Unsat c ↔ (∀ a, eval a c = false) := by rfl

@[simp] theorem unsat_empty : Unsat (.empty : Clause α) := by
  simp [unsat_def]

@[simp] theorem not_sat_empty {a : α → Bool} : ¬ Sat a (.empty : Clause α) := by
  simp [sat_def]

@[simp] theorem sat_add {a : α → Bool} {c : Clause α} :
    Sat a (c.add atom pol) ↔ a atom = pol ∨ Sat a c := by
  simp [sat_def]

@[simp] theorem sat_append {a : α → Bool} {c1 c2 : Clause α} :
    Sat a (c1 ++ c2) ↔ Sat a c1 ∨ Sat a c2 := by
  simp [sat_def]

theorem sat_append_left {a : α → Bool} {c1 c2 : Clause α} (h : Sat a c1) : Sat a (c1 ++ c2) :=
  sat_append.mpr (Or.inl h)

theorem sat_append_right {a : α → Bool} {c1 c2 : Clause α} (h : Sat a c2) : Sat a (c1 ++ c2) :=
  sat_append.mpr (Or.inr h)

@[simp] theorem unsat_append {c1 c2 : Clause α} : Unsat (c1 ++ c2) ↔ Unsat c1 ∧ Unsat c2 := by
  simp [unsat_def, forall_and]

theorem unsat_of_unsat_append_left {c1 c2 : Clause α} (h : Unsat (c1 ++ c2)) : Unsat c1 :=
  (unsat_append.mp h).left

theorem unsat_of_unsat_append_right {c1 c2 : Clause α} (h : Unsat (c1 ++ c2)) : Unsat c2 :=
  (unsat_append.mp h).right

theorem unsat_iff_not_sat {c : Clause α} : Unsat c ↔ ∀ a, ¬Sat a c := by
  rw [unsat_def]
  constructor
  · intro h1 a h2
    rw [sat_def] at h2
    simp_all
  · intro h1 a
    specialize h1 a
    rw [sat_def] at h1
    simp_all

theorem sat_iff_exists_mem_eq {c : Clause α} :
    Sat a c ↔ (∃ lit ∈ c, a lit.1 = lit.2) := by
  simp [sat_def, Membership.mem, eval]

theorem sat_of_mem_of_eq {c : Clause α} {lit : Literal α} (h1 : lit ∈ c) (h2 : a lit.1 = lit.2) :
    Sat a c :=
  sat_iff_exists_mem_eq.mpr ⟨lit, h1, h2⟩

theorem not_sat_iff_forall_mem_ne {c : Clause α} :
    (¬ Sat a c) ↔ (∀ lit ∈ c, a lit.1 ≠ lit.2) := by
  rw [sat_iff_exists_mem_eq]
  simp only [not_exists, not_and, ne_eq]

theorem sat_of_mem_of_mem_neg {c : Clause α} {atom : α} (h1 : (atom, pol) ∈ c)
    (h2 : (atom, !pol) ∈ c) : ∀ a, Sat a c := by
  intro a
  rw [sat_iff_exists_mem_eq]
  by_cases h3 : a atom = pol
  · exists (atom, pol)
  · exists (atom, !pol)
    cases pol <;> simp_all

open Classical in
theorem unsat_iff_eq_empty {c : Clause α} : Unsat c ↔ c = .empty := by
  constructor
  · intro h
    by_cases hc : c = .empty
    · exact hc
    · exfalso
      rcases exists_eq_add_of_ne_empty hc with ⟨c', atom, pol, rfl⟩
      apply unsat_iff_not_sat.mp h (fun v => if v = atom then pol else true)
      exact sat_add.mpr (Or.inl (by simp))
  · rintro rfl
    exact unsat_empty

end Clause

/--
Evaluating a `CNF` formula with respect to an assignment `a`.
-/
@[expose]
def eval (a : α → Bool) (f : CNF α) : Bool := f.clauses.all fun c => c.eval a

@[simp] theorem eval_empty (a : α → Bool) : eval a .empty = true := by simp [eval, empty]
@[simp] theorem eval_add (a : α → Bool) : eval a (f.add c) = (c.eval a && eval a f) := by
  rw [Bool.and_comm]
  simp [add, eval]

@[simp] theorem eval_append (a : α → Bool) (f1 f2 : CNF α) :
    eval a (f1 ++ f2) = (eval a f1 && eval a f2) := by
  simp [eval, Internal.clauses_append]

theorem eval_congr (a1 a2 : α → Bool) (f : CNF α) (hw : ∀ v, VarMem v f → a1 v = a2 v) :
    eval a1 f = eval a2 f := by
  rcases f with ⟨clauses⟩
  simp only [eval]
  rw [Bool.eq_iff_iff, Array.all_eq_true, Array.all_eq_true]
  constructor
  · intro h x hx
    rw [Clause.eval_congr a2 a1 clauses[x]]
    · exact h x hx
    · intro i hi
      symm
      exact hw _ (VarMem_of (by simp [Internal.mem_iff]) hi)
  · intro h x hx
    rw [Clause.eval_congr a1 a2 clauses[x]]
    · exact h x hx
    · intro i hi
      exact hw _ (VarMem_of (by simp [Internal.mem_iff]) hi)

@[expose] def Sat (a : α → Bool) (f : CNF α) : Prop := eval a f = true
@[expose] def Unsat (f : CNF α) : Prop := ∀ a, eval a f = false

theorem sat_def (a : α → Bool) (f : CNF α) : Sat a f ↔ (eval a f = true) := by rfl
theorem unsat_def (f : CNF α) : Unsat f ↔ (∀ a, eval a f = false) := by rfl

@[simp] theorem not_unsat_empty : ¬Unsat (.empty : CNF α) :=
  fun h => by simp [unsat_def] at h

@[simp] theorem sat_empty {assign : α → Bool} : Sat assign (.empty : CNF α) := by
  simp [sat_def]

@[simp]
theorem sat_add {assign : α → Bool} {f : CNF α} :
    Sat assign (f.add c : CNF α) ↔ (Clause.Sat assign c ∧ Sat assign f) := by
  simp [sat_def, Clause.sat_def]

@[simp]
theorem sat_append {assign : α → Bool} :
    Sat assign (f1 ++ f2 : CNF α) ↔ (Sat assign f1 ∧ Sat assign f2) := by
  simp [sat_def]

@[simp] theorem unsat_add_empty {g : CNF α} : Unsat (g.add .empty) := by
  simp [unsat_def]

theorem unsat_iff_not_sat {f : CNF α} : Unsat f ↔ ∀ a, ¬Sat a f := by
  rw [unsat_def]
  constructor
  · intro h1 a h2
    rw [sat_def] at h2
    simp_all
  · intro h1 a
    specialize h1 a
    rw [sat_def] at h1
    simp_all

theorem sat_iff_all_mem_sat {f : CNF α} {a : α → Bool} : Sat a f ↔ ∀ c ∈ f, Clause.Sat a c := by
  simp only [sat_def, Clause.sat_def, eval, Internal.mem_iff]
  rw [Array.all_eq_true_iff_forall_mem]

theorem sat_of_all_mem_sat {f : CNF α} {a : α → Bool} : (∀ c ∈ f, Clause.Sat a c) → Sat a f := by
  simp [sat_iff_all_mem_sat]

theorem sat_of_mem {f : CNF α} (h1 : Sat a f) (h2 : c ∈ f) : Clause.Sat a c :=
  sat_iff_all_mem_sat.mp h1 c h2

theorem not_sat_iff_exists_mem_not_sat {f : CNF α} :
    (¬Sat a f) ↔ (∃ c ∈ f, ¬Clause.Sat a c) := by
  simp only [sat_def, Clause.sat_def, eval, Bool.not_eq_true, Array.all_eq_false',
    Internal.mem_iff]

theorem unsat_of_mem_unsat {f : CNF α} (h1 : c ∈ f) (h2 : Clause.Unsat c) : Unsat f := by
  rw [unsat_iff_not_sat]
  intro a hsat
  exact Clause.unsat_iff_not_sat.mp h2 a (sat_of_mem hsat h1)

theorem unsat_add_of_clause_unsat {f : CNF α} (h : Clause.Unsat c) : Unsat (f.add c) :=
  unsat_of_mem_unsat (by simp) h

theorem unsat_add_of_unsat {f : CNF α} (h : Unsat f) : Unsat (f.add c) := by
  rw [unsat_iff_not_sat] at h ⊢
  intro a hsat
  exact h a (sat_add.mp hsat).right

theorem unsat_append_left {f1 f2 : CNF α} (h : Unsat f1) : Unsat (f1 ++ f2) := by
  rw [unsat_iff_not_sat] at h ⊢
  intro a hsat
  exact h a (sat_append.mp hsat).left

theorem unsat_append_right {f1 f2 : CNF α} (h : Unsat f2) : Unsat (f1 ++ f2) := by
  rw [unsat_iff_not_sat] at h ⊢
  intro a hsat
  exact h a (sat_append.mp hsat).right

theorem unsat_of_forall_exists {c1 c2 : CNF α} (h : ∀ a, Sat a c1 → ∃ a', Sat a' c2) :
    Unsat c2 → Unsat c1 := by
  rw [unsat_iff_not_sat, unsat_iff_not_sat]
  intro h2 a h3
  rcases h a h3 with ⟨a', ha'⟩
  exact h2 a' ha'

end CNF

end Sat
end Std
