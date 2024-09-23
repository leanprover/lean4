/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Sat.CNF.RelabelFin
import Std.Tactic.BVDecide.LRAT.Internal.Formula

namespace Std.Tactic.BVDecide

namespace LRAT
namespace Internal

open Std.Sat
open Entails


/--
Turn a `CNF Nat`, that might contain `0` as a variable, to a `CNF PosFin`.
This representation is guaranteed to not have `0` and is limited to an upper bound of
variable indices.
-/
def CNF.lift (cnf : CNF Nat) : CNF (PosFin (cnf.numLiterals + 1)) :=
  let cnf := cnf.relabelFin
  cnf.relabel (fun lit => ⟨lit.val + 1, by omega⟩)

theorem CNF.unsat_of_lift_unsat (cnf : CNF Nat) :
    (CNF.lift cnf).Unsat → cnf.Unsat := by
  intro h2
  have h3 :=
    CNF.unsat_relabel_iff
      (by
        intro a b ha hb hab
        injections hab
        cases a; cases b; simp_all)
      |>.mp h2
  exact CNF.unsat_relabelFin.mp h3

/--
Turn a `CNF.Clause PosFin` into the representation used by the LRAT checker.
-/
def CNF.Clause.convertLRAT' (clause : CNF.Clause (PosFin n)) : Option (DefaultClause n) :=
  DefaultClause.ofArray clause.toArray

/--
Turn a `CNF PosFin` into the representation used by the LRAT checker.
-/
def CNF.convertLRAT' (clauses : CNF (PosFin n)) : List (Option (DefaultClause n)) :=
  clauses.filterMap (fun clause =>
    match CNF.Clause.convertLRAT' clause with
    | some clause => some clause
    -- This might look stupid but we are in an Option (Option x) here so explicitly returning none
    -- is different from not doing this pattern match.
    | none => none
  )

theorem CNF.Clause.mem_lrat_of_mem (clause : CNF.Clause (PosFin n)) (h1 : l ∈ clause)
    (h2 : DefaultClause.ofArray clause.toArray = some lratClause) : l ∈ lratClause.clause := by
  induction clause generalizing lratClause with
  | nil => cases h1
  | cons hd tl ih =>
    unfold DefaultClause.ofArray at h2
    rw [Array.foldr_eq_foldr_toList, List.toArray_toList] at h2
    dsimp only [List.foldr] at h2
    split at h2
    · cases h2
    · rw [DefaultClause.insert] at h2
      split at h2
      · cases h2
      · split at h2
        · rename_i h
          rw [← Option.some.inj h2] at *
          cases h1
          · exact List.mem_of_elem_eq_true h
          · apply ih
            · assumption
            · next heq _ _ =>
              unfold DefaultClause.ofArray
              rw [Array.foldr_eq_foldr_toList, List.toArray_toList]
              exact heq
        · cases h1
          · simp only [← Option.some.inj h2]
            constructor
          · simp only at h2
            simp only [← Option.some.inj h2]
            rename_i heq _ _ _
            apply List.Mem.tail
            apply ih
            assumption
            unfold DefaultClause.ofArray
            rw [Array.foldr_eq_foldr_toList, List.toArray_toList]
            exact heq

theorem CNF.Clause.convertLRAT_sat_of_sat (clause : CNF.Clause (PosFin n))
    (h : Clause.convertLRAT' clause = some lratClause) :
    clause.eval assign → assign ⊨ lratClause := by
  intro h2
  simp only [CNF.Clause.eval, List.any_eq_true, bne_iff_ne, ne_eq] at h2
  simp only [(· ⊨ ·), Clause.eval, List.any_eq_true, decide_eq_true_eq]
  rcases h2 with ⟨lit, ⟨hlit1, hlit2⟩⟩
  apply Exists.intro lit
  constructor
  · simp only [Clause.toList, DefaultClause.toList]
    simp only [convertLRAT'] at h
    exact CNF.Clause.mem_lrat_of_mem clause hlit1 h
  · simp_all

/--
Convert a `CNF Nat` with a certain maximum variable number into the `DefaultFormula`
format for usage with `bv_decide`'s `LRAT.Internal`.

Notably this:
1. Increments all variables as DIMACS variables start at 1 instead of 0
2. Adds a leading `none` clause. This clause *must* be persistent as the LRAT checker wants to have
  the DIMACS file line by line and the DIMACS file begins with the `p cnf x y` meta instruction.
-/
def CNF.convertLRAT (cnf : CNF Nat) : DefaultFormula (cnf.numLiterals + 1) :=
  let lifted := CNF.lift cnf
  let lratCnf := CNF.convertLRAT' lifted
  DefaultFormula.ofArray (none :: lratCnf).toArray

theorem CNF.convertLRAT_readyForRupAdd (cnf : CNF Nat) :
    DefaultFormula.ReadyForRupAdd (CNF.convertLRAT cnf) := by
  unfold CNF.convertLRAT
  apply DefaultFormula.readyForRupAdd_ofArray

theorem CNF.convertLRAT_readyForRatAdd (cnf : CNF Nat) :
    DefaultFormula.ReadyForRatAdd (CNF.convertLRAT cnf) := by
  unfold CNF.convertLRAT
  apply DefaultFormula.readyForRatAdd_ofArray

theorem unsat_of_cons_none_unsat (clauses : List (Option (DefaultClause n))) :
    Unsatisfiable (PosFin n) (DefaultFormula.ofArray (none :: clauses).toArray)
      →
    Unsatisfiable (PosFin n) (DefaultFormula.ofArray clauses.toArray) := by
  intro h assign hassign
  apply h assign
  simp only [Formula.formulaEntails_def, List.all_eq_true, decide_eq_true_eq] at *
  intro clause hclause
  simp_all[DefaultFormula.ofArray, Formula.toList, DefaultFormula.toList]

theorem CNF.unsat_of_convertLRAT_unsat (cnf : CNF Nat) :
    Unsatisfiable (PosFin (cnf.numLiterals + 1)) (CNF.convertLRAT cnf)
      →
    cnf.Unsat := by
  intro h1
  apply CNF.unsat_of_lift_unsat
  intro assignment
  unfold CNF.convertLRAT at h1
  replace h1 := (unsat_of_cons_none_unsat _ h1) assignment
  apply eq_false_of_ne_true
  intro h2
  apply h1
  simp only [Formula.formulaEntails_def, List.all_eq_true, decide_eq_true_eq]
  intro lratClause hlclause
  simp only [Formula.toList, DefaultFormula.toList, DefaultFormula.ofArray,
    CNF.convertLRAT', Array.size_toArray, List.length_map, Array.toList_toArray,
    List.map_nil, List.append_nil, List.mem_filterMap, List.mem_map, id_eq, exists_eq_right] at hlclause
  rcases hlclause with ⟨reflectClause, ⟨hrclause1, hrclause2⟩⟩
  simp only [CNF.eval, List.all_eq_true] at h2
  split at hrclause2
  · next heq =>
    rw [← heq] at hrclause2
    simp only [Option.some.injEq] at hrclause2
    simp [CNF.Clause.convertLRAT_sat_of_sat reflectClause hrclause2, h2 reflectClause hrclause1]
  · contradiction

end Internal
end LRAT
end Std.Tactic.BVDecide
