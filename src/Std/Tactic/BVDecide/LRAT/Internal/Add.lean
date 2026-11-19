/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Tactic.BVDecide.LRAT.Internal.Basic

namespace Std.Tactic.BVDecide.LRAT.Internal

open Std.Sat

namespace State

@[inline]
public def add (s : State) (clause : CNF.Clause Nat) : State :=
  { s with formula := s.formula.push (some clause) }

@[simp]
public theorem add_toCNF_eq_toCNF_add {s : State} {c : CNF.Clause Nat} :
    (s.add c).toCNF = s.toCNF.add c := by
  simp [toCNF, add, CNF.add]

public theorem entails_add_of_entails_clause {s : State} {c : CNF.Clause Nat}
    (h : CNF.EntailsClause s.toCNF c) : CNF.Entails s.toCNF (s.add c).toCNF := by
  rw [add_toCNF_eq_toCNF_add]
  apply CNF.entails_add_of_entails_clause
  exact h

end State

end Std.Tactic.BVDecide.LRAT.Internal
