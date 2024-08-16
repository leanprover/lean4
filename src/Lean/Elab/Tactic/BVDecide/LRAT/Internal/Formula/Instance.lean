/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
prelude
import Lean.Elab.Tactic.BVDecide.LRAT.Internal.Formula.RatAddSound

/-!
This module couples the default LRAT implementation to the `Formula` typeclass.
-/

namespace Lean.Elab.Tactic.BVDecide
namespace LRAT
namespace Internal

namespace DefaultFormula

instance {n : Nat} : Formula (PosFin n) (DefaultClause n) (DefaultFormula n) where
  toList := toList
  ReadyForRupAdd := ReadyForRupAdd
  ReadyForRatAdd := ReadyForRatAdd
  ofArray := ofArray
  ofArray_readyForRupAdd := ofArray_readyForRupAdd
  ofArray_readyForRatAdd := ofArray_readyForRatAdd
  insert := insert
  insert_iff := insert_iff
  insert_readyForRupAdd := insert_readyForRupAdd
  insert_readyForRatAdd := insert_readyForRatAdd
  delete := delete
  delete_readyForRupAdd := delete_readyForRupAdd
  delete_readyForRatAdd := delete_readyForRatAdd
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
end Lean.Elab.Tactic.BVDecide
