/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Tactic.BVDecide.LRAT.Internal.Basic
import Init.ByCases

namespace Std.Tactic.BVDecide.LRAT.Internal

open Std.Sat

namespace State

@[inline]
def deleteOne (s : State) (idx : Nat) : State :=
  { s with formula := s.formula.setIfInBounds (idx - 1) none }

theorem entails_deleteOne {s : State} : CNF.Entails s.toCNF (s.deleteOne idx).toCNF := by
  apply CNF.entails_of_all_mem
  intro c hc
  rcases exists_get?_eq_some_of_mem hc with ⟨idx', hidx'⟩
  simp only [get?, deleteOne, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds] at hidx'
  split at hidx'
  · split at hidx' <;> simp at hidx'
  · apply mem_toCNF_of_eq_some (idx := idx')
    simp_all [get?]

public def deleteMany (s : State) (idxs : Array Nat) : State :=
  idxs.foldl (init := s) State.deleteOne

public theorem entails_deleteMany {s : State} :
    CNF.Entails s.toCNF (s.deleteMany idxs).toCNF := by
  unfold deleteMany
  apply Array.foldl_induction (motive := fun _ (s' : State) => CNF.Entails s.toCNF s'.toCNF)
  · rfl
  · intro i b h
    apply CNF.entails_trans
    · exact h
    · exact entails_deleteOne

end State

end Std.Tactic.BVDecide.LRAT.Internal
