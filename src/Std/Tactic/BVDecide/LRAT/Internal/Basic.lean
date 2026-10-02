/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Sat.CNF.Basic
public import Std.Sat.CNF.Entails
import Init.Omega

public section

namespace Std.Tactic.BVDecide.LRAT.Internal

open Std.Sat

structure State where
  formula : Array (Option (CNF.Clause Nat))

namespace State

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

/--
Check that `p` holds for all clauses of `s`, together with the index they are stored at.

This iterates over the underlying array instead of `s.toCNF`, which would have to be materialized.
-/
@[inline]
def all (s : State) (p : Nat → CNF.Clause Nat → Bool) : Bool :=
  go 0
where
  @[specialize] go (i : Nat) : Bool :=
    if h : i < s.formula.size then
      match s.formula[i] with
      | some c => p (i + 1) c && go (i + 1)
      | none => go (i + 1)
    else
      true
  termination_by s.formula.size - i

theorem mem_toCNF_of_eq_some {s : State} (h : s.get? idx = some c) : c ∈ s.toCNF := by
  rw [get?, Array.getD_eq_getD_getElem?] at h
  rcases h' : s.formula[idx - 1]? with _ | o
  · simp [h'] at h
  · rw [h'] at h
    simp only [Option.getD_some] at h
    subst h
    rw [toCNF, CNF.Internal.mem_iff]
    exact Array.mem_filterMap.mpr ⟨some c, Array.mem_of_getElem? h', rfl⟩

theorem exists_getElem_eq_some_of_mem {s : State} (h : c ∈ s.toCNF) :
    ∃ (i : Nat) (hi : i < s.formula.size), s.formula[i] = some c := by
  rw [toCNF, CNF.Internal.mem_iff] at h
  rcases Array.mem_filterMap.mp h with ⟨o, hmem, ho⟩
  simp only [id_eq] at ho
  subst ho
  rcases Array.mem_iff_getElem.mp hmem with ⟨i, hi, hig⟩
  exact ⟨i, hi, hig⟩

theorem get?_add_one_of_getElem_eq_some {s : State} {i : Nat} (hi : i < s.formula.size)
    (h : s.formula[i] = some c) : s.get? (i + 1) = some c := by
  simp [get?, hi, h]

theorem exists_get?_eq_some_of_mem {s : State} (h : c ∈ s.toCNF) :
    ∃ idx, s.get? idx = some c := by
  rcases exists_getElem_eq_some_of_mem h with ⟨i, hi, hig⟩
  exact ⟨i + 1, get?_add_one_of_getElem_eq_some hi hig⟩

private theorem all_go_eq_true_iff {s : State} {p : Nat → CNF.Clause Nat → Bool} {i : Nat} :
    all.go s p i = true ↔
      ∀ (j : Nat) (hj : j < s.formula.size), i ≤ j →
        ∀ c, s.formula[j] = some c → p (j + 1) c = true := by
  fun_induction all.go s p i with
  | case1 i h c hc ih =>
    rw [Bool.and_eq_true, ih]
    constructor
    · rintro ⟨hp, hrest⟩ j hj hij c' hc'
      rcases Nat.eq_or_lt_of_le hij with rfl | hij
      · rw [hc] at hc'
        obtain rfl : c = c' := by simpa using hc'
        exact hp
      · exact hrest j hj hij c' hc'
    · intro hall
      exact ⟨hall i h (Nat.le_refl _) c hc, fun j hj hij c' hc' => hall j hj (by omega) c' hc'⟩
  | case2 i h hc ih =>
    rw [ih]
    constructor
    · intro hrest j hj hij c' hc'
      rcases Nat.eq_or_lt_of_le hij with rfl | hij
      · rw [hc] at hc'
        simp at hc'
      · exact hrest j hj hij c' hc'
    · exact fun hall j hj hij c' hc' => hall j hj (by omega) c' hc'
  | case3 i h =>
    simp only [true_iff]
    intros
    omega

theorem all_eq_true_iff {s : State} {p : Nat → CNF.Clause Nat → Bool} :
    s.all p = true ↔
      ∀ (j : Nat) (hj : j < s.formula.size), ∀ c, s.formula[j] = some c → p (j + 1) c = true := by
  rw [all, all_go_eq_true_iff]
  exact ⟨fun h j hj c hc => h j hj (Nat.zero_le _) c hc, fun h j hj _ c hc => h j hj c hc⟩

theorem forall_of_all_eq_true {s : State} {p : Nat → CNF.Clause Nat → Bool} (h : s.all p) :
    ∀ c ∈ s.toCNF, ∃ idx, s.get? idx = some c ∧ p idx c := by
  intro c hc
  rcases exists_getElem_eq_some_of_mem hc with ⟨i, hi, hig⟩
  exact ⟨i + 1, get?_add_one_of_getElem_eq_some hi hig, all_eq_true_iff.mp h i hi c hig⟩

end State

end Std.Tactic.BVDecide.LRAT.Internal
