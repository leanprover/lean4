/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Sat.CNF.Basic
public import Std.Sat.CNF.Sat
public import Std.Sat.CNF.Relabel
public import Std.Sat.CNF.Entails
import Init.ByCases

public section

namespace Std
namespace Sat

namespace CNF
namespace Clause

def unit (atom : α) (pol : Bool) : Clause α := Clause.empty.add atom pol

theorem unit_def : unit atom pol = Clause.empty.add atom pol := by
  simp [unit]

@[simp]
theorem eval_unit : eval a (unit atom pol) = (a atom == pol) := by
  simp [unit_def]

@[simp]
theorem mem_unit {l : Literal α} : l ∈ unit atom pol ↔ l = (atom, pol) := by
  simp [unit_def]

theorem unit_ne_empty {atom : α} : unit atom pol ≠ (empty : Clause α) := by
  simp [unit_def]

@[simp]
theorem VarMem_unit {v : α} : VarMem v (unit atom pol) ↔ v = atom := by
  simp [unit_def]

@[simp]
theorem relabel_unit {r : α → β} : relabel r (unit atom pol) = unit (r atom) pol := by
  simp [unit_def]

@[simp]
theorem sat_unit_iff : Sat a (unit atom pol) ↔ a atom = pol := by
  simp [unit_def]

@[simp]
theorem not_sat_unit_iff : (¬Sat a (unit atom pol)) ↔ a atom = !pol := by
  cases pol <;> simp

@[simp]
theorem not_unsat_unit : ¬ Unsat (unit atom p) := by
  simp [unit_def, unsat_iff_eq_empty]

end Clause

@[simp]
theorem sat_add_unit_iff (f : CNF α) (atom : α) (pol : Bool) :
    Sat a (f.add (.unit atom pol)) ↔ (a atom = pol ∧ Sat a f) := by
  simp

theorem entails_clause_unit_iff_unsat_add_neg {f : CNF α} {atom : α} {pol : Bool} :
    EntailsClause f (.unit atom pol) ↔ Unsat (f.add (.unit atom (!pol))) := by
  rw [entails_clause_def, unsat_iff_not_sat]
  simp only [sat_add, Clause.sat_unit_iff, not_and]
  constructor
  · intro h a hval hsat
    have := h a hsat
    simp_all
  · intro h1 a hsat
    apply Classical.byContradiction
    intro h2
    specialize h1 a
    simp_all

end CNF
end Sat
end Std
