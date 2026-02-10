/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Tactic.BVDecide.LRAT.Internal.Convert
public import Std.Tactic.BVDecide.LRAT.Internal.LRATCheckerSound

@[expose] public section

/-!
This module contains the implementation of the LRAT checker as well as a proof that the given
CNF is unsat if the checker succeeds.
-/

open Std.Sat

namespace Std.Tactic.BVDecide
namespace LRAT

open Std.Tactic.BVDecide.LRAT.Internal
/--
Check whether `lratProof` is a valid LRAT certificate for the unsatisfiability of `cnf`.
-/
def check (lratProof : Array IntAction) (cnf : CNF Nat) : Bool :=
  let internalFormula := CNF.convertLRAT cnf
  let checkerResult := go internalFormula lratProof 0
  checkerResult = .success
where
  go  {n : Nat} (f : DefaultFormula n) (proof : Array IntAction) (idx : Nat) : Result :=
    if h : idx < proof.size then
      let step := intActionToDefaultClauseAction n proof[idx]
      match step with
      | none => go f proof (idx + 1)
      | some (.addEmpty _ rupHints) =>
        let (_, checkSuccess) := Formula.performRupAdd f Clause.empty rupHints
        if checkSuccess then
          .success
        else
          .rupFailure
      | some (.addRup _ c rupHints) =>
        let (f, checkSuccess) := Formula.performRupAdd f c rupHints
        if checkSuccess then
          go f proof (idx + 1)
        else
          .rupFailure
      | some (.addRat _ c pivot rupHints ratHints) =>
        if pivot ∈ Clause.toList c then
          let (f, checkSuccess) := Formula.performRatAdd f c pivot rupHints ratHints
          if checkSuccess then
            go f proof (idx + 1)
          else
            .rupFailure
        else
          go f proof (idx + 1)
      | some (.del ids) => go (Formula.delete f ids) proof (idx + 1)
    else
      .outOfProof

theorem go_sound (f : DefaultFormula n) (proof : Array IntAction) (idx : Nat)
    (h1 : Formula.ReadyForRupAdd f) (h2 : Formula.ReadyForRatAdd f) :
    check.go f proof idx = .success → Unsatisfiable (PosFin n) f := by
  fun_induction check.go
  case case1 ih1 => apply ih1 <;> assumption
  case case2 f _ _ _ _ hints _ f' h3 =>
    intro _ p pf
    have f'_def : f' = Formula.insert f Clause.empty := by grind
    have f_liff_f' : Liff (PosFin n) f (Formula.insert f Clause.empty) := by grind
    specialize f_liff_f' p
    rw [f_liff_f', Formula.sat_iff_forall] at pf
    have empty_in_f' : Clause.empty ∈ Formula.toList (Formula.insert f Clause.empty) := by grind
    simp only [(· ⊨ ·)] at pf
    grind [Clause.eval]
  case case3 => simp
  case case4 => grind [Unsatisfiable, Liff]
  case case5 => simp
  case case6 => grind [Equisat, Clause.limplies_iff_mem]
  case case7 => simp
  case case8 ih1 => apply ih1 <;> assumption
  case case9 ih1 =>
    intro h3
    intro p pf
    specialize ih1 (by grind) (by grind) h3 p
    apply ih1
    apply Formula.limplies_delete
    assumption
  case case10 => simp

open Std.Tactic.BVDecide.LRAT.Internal in
/--
If the `check` functions succeeds on `lratProof` and `cnf` then the `cnf` is unsatisfiable.
-/
theorem check_sound (lratProof : Array IntAction) (cnf : CNF Nat) :
    check lratProof cnf → cnf.Unsat := by
  intro h1
  apply CNF.unsat_of_convertLRAT_unsat
  unfold check at h1
  simp at h1
  apply go_sound (proof := lratProof) (idx := 0)
  · apply CNF.convertLRAT_readyForRupAdd
  · apply CNF.convertLRAT_readyForRatAdd
  · assumption

end LRAT
end Std.Tactic.BVDecide
