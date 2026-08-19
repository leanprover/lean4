/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Sat.CNF.Basic
public import Std.Sat.CNF.Entails

public section

namespace Std.Tactic.BVDecide.LRAT.NewInternal

open Std.Sat

structure State where
  formula : Array (Option (CNF.Clause Nat))

namespace State

@[expose]
def ofCNF (cnf : CNF Nat) : State :=
  ⟨cnf.clauses.map fun clause => some clause⟩

@[expose]
def toCNF (s : State) : CNF Nat :=
  ⟨s.formula.filterMap id⟩

@[simp]
theorem ofCNF_toCNF_eq {cnf : CNF Nat} : (ofCNF cnf).toCNF = cnf := by
  rw [CNF.Internal.ext_iff]
  show Array.filterMap id (cnf.clauses.map (fun clause => some clause)) = cnf.clauses
  rw [Array.filterMap_map]
  simp

theorem entails_ofCNF_toCNF {cnf : CNF Nat} : CNF.Entails cnf (ofCNF cnf).toCNF := by
  rw [ofCNF_toCNF_eq]

@[inline, expose]
def get? (s : State) (idx : Nat) : Option (CNF.Clause Nat) :=
  s.formula.getD (idx - 1) none

theorem mem_toCNF_of_eq_some {s : State} (h : s.get? idx = some c) : c ∈ s.toCNF := by
  rw [get?, Array.getD_eq_getD_getElem?] at h
  rcases h' : s.formula[idx - 1]? with _ | o
  · simp [h'] at h
  · rw [h'] at h
    simp only [Option.getD_some] at h
    subst h
    rw [toCNF, CNF.Internal.mem_iff]
    exact Array.mem_filterMap.mpr ⟨some c, Array.mem_of_getElem? h', rfl⟩

theorem exists_get?_eq_some_of_mem {s : State} (h : c ∈ s.toCNF) :
    ∃ idx, s.get? idx = some c := by
  rw [toCNF, CNF.Internal.mem_iff] at h
  rcases Array.mem_filterMap.mp h with ⟨o, hmem, ho⟩
  simp only [id_eq] at ho
  subst ho
  rcases Array.mem_iff_getElem.mp hmem with ⟨i, hi, hig⟩
  refine ⟨i + 1, ?_⟩
  simp [get?, hi, hig]

end State

end Std.Tactic.BVDecide.LRAT.NewInternal
