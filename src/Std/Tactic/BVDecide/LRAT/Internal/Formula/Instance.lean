/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
prelude
import Std.Tactic.BVDecide.LRAT.Internal.Formula.RatAddSound

/-!
This module couples the default LRAT implementation to the `Formula` typeclass.
-/

namespace Std.Tactic.BVDecide
namespace LRAT
namespace Internal

namespace DefaultFormula

instance {n : Nat} : Formula (PosFin n) (DefaultClause n) (DefaultFormula n) where
  toList := toList
  ReadyForRupAdd := ReadyForRupAdd
  ReadyForRatAdd := ReadyForRatAdd
  ofArray := ofArray
  readyForRupAdd_ofArray := readyForRupAdd_ofArray
  readyForRatAdd_ofArray := readyForRatAdd_ofArray
  insert := insert
  insert_iff := insert_iff
  readyForRupAdd_insert := readyForRupAdd_insert
  readyForRatAdd_insert := readyForRatAdd_insert
  delete := delete
  readyForRupAdd_delete := readyForRupAdd_delete
  readyForRatAdd_delete := readyForRatAdd_delete
  delete_subset := delete_subset
  formulaEntails_def := formulaEntails_def
  performRupAdd := performRupAdd
  rupAdd_result := rupAdd_result
  rupAdd_sound := rupAdd_sound
  performRatAdd := performRatAdd
  ratAdd_result := ratAdd_result
  ratAdd_sound := ratAdd_sound

end DefaultFormula

end Internal
end LRAT
end Std.Tactic.BVDecide
