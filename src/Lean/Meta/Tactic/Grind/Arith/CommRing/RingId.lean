/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.CommRing.RingM
import Lean.Meta.Sym.Arith.Classify
public section
namespace Lean.Meta.Grind.Arith.CommRing
open Sym.Arith

/-!
Ring ids are assigned by `Sym.Arith.classify?`, which tries `CommRing`, `Ring`,
`CommSemiring`, and `Semiring` in this order and caches the result for the whole run.
The functions below select one class of the result; a type has at most one.
-/

/-- Returns the ring id for the given type if there is a `CommRing` instance for it. -/
def getCommRingId? (type : Expr) : GoalM (Option Nat) := do
  let .commRing id ← classify? type | return none
  return some id

/-- Returns the ring id for the given type if it is a non-commutative `Ring`. -/
def getNonCommRingId? (type : Expr) : GoalM (Option Nat) := do
  let .nonCommRing id ← classify? type | return none
  return some id

/-- Returns the semiring id for the given type if it is a `CommSemiring` (and not a `CommRing`). -/
def getCommSemiringId? (type : Expr) : GoalM (Option Nat) := do
  let .commSemiring id ← classify? type | return none
  return some id

/-- Returns the semiring id for the given type if it is a non-commutative `Semiring`. -/
def getNonCommSemiringId? (type : Expr) : GoalM (Option Nat) := do
  let .nonCommSemiring id ← classify? type | return none
  return some id

end Lean.Meta.Grind.Arith.CommRing
