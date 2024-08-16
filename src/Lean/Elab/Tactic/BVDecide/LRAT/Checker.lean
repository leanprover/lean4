/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Lean.Elab.Tactic.BVDecide.LRAT.Actions
import Lean.Elab.Tactic.BVDecide.LRAT.Internal.Convert
import Lean.Elab.Tactic.BVDecide.LRAT.Internal.LRATChecker
import Lean.Elab.Tactic.BVDecide.LRAT.Internal.LRATCheckerSound
import Std.Sat.CNF

/-!
This module contains the implementation of the LRAT checker as well as a proof that the given
CNF is unsat if the checker succeeds.
-/

open Std.Sat

namespace Lean.Elab.Tactic.BVDecide
namespace LRAT

open Lean.Elab.Tactic.BVDecide.LRAT.Internal in
/--
Check whether `lratProof` is a valid LRAT certificate for the unsatisfiability of `cnf`.
-/
def check (lratProof : Array IntAction) (cnf : CNF Nat) : Bool :=
  let internalFormula := CNF.convertLRAT cnf
  let lratProof := lratProof.toList
  let lratProof := lratProof.map (intActionToDefaultClauseAction _)
  let lratProof : List { act // WellFormedAction act } :=
    lratProof.filterMap
      (fun actOpt =>
        match actOpt with
        | none => none
        | some (LRAT.Action.addEmpty id rupHints) =>
          some ⟨LRAT.Action.addEmpty id rupHints, by simp only [WellFormedAction]⟩
        | some (LRAT.Action.addRup id c rupHints) =>
          some ⟨LRAT.Action.addRup id c rupHints, by simp only [WellFormedAction]⟩
        | some (LRAT.Action.del ids) =>
          some ⟨LRAT.Action.del ids, by simp only [WellFormedAction]⟩
        | some (LRAT.Action.addRat id c pivot rupHints ratHints) =>
          if h : pivot ∈ Clause.toList c then
            some ⟨
              LRAT.Action.addRat id c pivot rupHints ratHints,
              by simp [WellFormedAction, Clause.limplies_iff_mem, h]
            ⟩
          else
            none
      )
  let lratProof := lratProof.map Subtype.val
  let checkerResult := lratChecker internalFormula lratProof
  checkerResult = .success

open Lean.Elab.Tactic.BVDecide.LRAT.Internal in
/--
If the `check` functions succeeds on `lratProof` and `cnf` then the `cnf` is unsatisfiable.
-/
theorem check_sound (lratProof : Array IntAction) (cnf : CNF Nat) :
    check lratProof cnf → cnf.Unsat := by
  intro h1
  unfold check at h1
  simp only [decide_eq_true_eq] at h1
  have h2 :=
    lratCheckerSound
      _
      (by apply CNF.convertLRAT_readyForRupAdd)
      (by apply CNF.convertLRAT_readyForRatAdd)
      _
      (by
        intro action h
        simp only [List.mem_map, List.mem_filterMap] at h
        rcases h with ⟨WellFormedActions, _, h2⟩
        rw [← h2]
        exact WellFormedActions.property)
      h1
  apply CNF.unsat_of_convertLRAT_unsat
  assumption

end LRAT
end Lean.Elab.Tactic.BVDecide
