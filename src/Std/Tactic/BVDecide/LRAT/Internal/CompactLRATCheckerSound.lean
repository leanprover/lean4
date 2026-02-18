/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Tactic.BVDecide.LRAT.Internal.CompactLRATChecker
import Std.Tactic.BVDecide.LRAT.Internal.LRATCheckerSound

namespace Std.Tactic.BVDecide
namespace LRAT
namespace Internal

theorem go_sound (f : DefaultFormula n) (proof : Array IntAction) (idx : Nat)
    (h1 : Formula.ReadyForRupAdd f) (h2 : Formula.ReadyForRatAdd f) :
    compactLratChecker.go f proof idx = .success → Unsatisfiable (PosFin n) f := by
  fun_induction compactLratChecker.go
  case case1 ih1 => apply ih1 <;> assumption
  case case2 _ _ _ _ _ hints _ _ h3 =>
    intro _
    apply addEmptyCaseSound (rupHints := hints)
    · assumption
    · simp [h3]
  case case3 => simp
  case case4 => grind [Unsatisfiable, Liff]
  case case5 => simp
  case case6 => grind [Equisat, Clause.limplies_iff_mem]
  case case7 => simp
  case case8 ih1 => apply ih1 <;> assumption
  case case9 ih1 =>
    intro h3 p pf
    apply ih1 (by grind) (by grind) h3 p
    apply Formula.limplies_delete
    assumption
  case case10 => simp

public theorem compactLratChecker_sound (f : DefaultFormula n) (proof : Array IntAction)
    (h1 : Formula.ReadyForRupAdd f) (h2 : Formula.ReadyForRatAdd f) :
    compactLratChecker f proof = .success → Unsatisfiable (PosFin n) f := by
  apply go_sound <;> assumption

end Internal
end LRAT
end Std.Tactic.BVDecide
