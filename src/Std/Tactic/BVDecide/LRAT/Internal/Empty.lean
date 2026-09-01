/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Tactic.BVDecide.LRAT.Internal.Rup

public section

namespace Std.Tactic.BVDecide.LRAT.Internal

open Std.Sat

namespace State

def checkEmpty (s : State) (rupHints : Array Nat) : Bool :=
  s.checkRup .empty rupHints

theorem entails_clause_empty_of_checkEmpty {s : State} {rupHints : Array Nat}
    (h : checkEmpty s rupHints = true) : CNF.EntailsClause s.toCNF .empty := by
  rw [checkEmpty] at h
  apply entails_clause_of_checkRup
  exact h

end State

end Std.Tactic.BVDecide.LRAT.Internal
