/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Tactic.BVDecide.LRAT.Actions
import Std.Tactic.BVDecide.LRAT.Internal.Convert
import Std.Tactic.BVDecide.LRAT.Internal.LRATChecker
import Std.Tactic.BVDecide.LRAT.Internal.LRATCheckerSound
import Std.Sat.CNF

/-!
This module contains the implementation of the LRAT checker as well as a proof that the given
CNF is unsat if the checker succeeds.
-/

open Std.Sat

namespace Std.Tactic.BVDecide
namespace LRAT

open Std.Tactic.BVDecide.LRAT.Internal in
/--
Check whether `lratProof` is a valid LRAT certificate for the unsatisfiability of `cnf`.
-/
def check (lratProof : Array IntAction) (cnf : CNF Nat) : Bool :=
  let internalFormula := CNF.convertLRAT cnf
  let lratProof := lratProof.toList
  let lratProof := lratProof.map (intActionToDefaultClauseAction _)
  let lratProof :=
    lratProof.filterMap
      (fun actOpt =>
        match actOpt with
        | none => none
        | some (LRAT.Action.addEmpty id rupHints) => some (LRAT.Action.addEmpty id rupHints)
        | some (LRAT.Action.addRup id c rupHints) => some (LRAT.Action.addRup id c rupHints)
        | some (LRAT.Action.del ids) => some (LRAT.Action.del ids)
        | some (LRAT.Action.addRat id c pivot rupHints ratHints) =>
          if pivot ∈ Clause.toList c then
            some (LRAT.Action.addRat id c pivot rupHints ratHints)
          else
            none
      )
  let checkerResult := lratChecker internalFormula lratProof
  checkerResult = .success

open Std.Tactic.BVDecide.LRAT.Internal in
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
        simp only [List.filterMap_map, List.mem_filterMap, Function.comp_apply] at h
        rcases h with ⟨WellFormedActions, _, h2⟩
        split at h2
        . contradiction
        . simp only [Option.some.injEq] at h2
          simp [← h2, WellFormedAction]
        . simp only [Option.some.injEq] at h2
          simp [← h2, WellFormedAction]
        . simp only [Option.some.injEq] at h2
          simp [← h2, WellFormedAction]
        . simp only [Option.ite_none_right_eq_some, Option.some.injEq] at h2
          rcases h2 with ⟨hleft, hright⟩
          simp [WellFormedAction, hleft, ← hright, Clause.limplies_iff_mem]
      )
      h1
  apply CNF.unsat_of_convertLRAT_unsat
  assumption

end LRAT
end Std.Tactic.BVDecide
