/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
prelude
import Std.Sat.CNF

/-!
This module contains the definition of the LRAT format (https://www.cs.utexas.edu/~marijn/publications/lrat.pdf)
as a type `Action`, that is polymorphic over the variables used in the CNF. The type
`IntAction := Action (Array Int) Nat` is the version that is used by the checker as input and should
be considered the parsing target for LRAT proofs.
-/

namespace Std.Tactic.BVDecide
namespace LRAT

open Std.Sat

/-- `β` is for the type of a clause, `α` is for the type of variables -/
inductive Action (β : Type u) (α : Type v)
  | addEmpty (id : Nat) (rupHints : Array Nat)
  | addRup (id : Nat) (c : β) (rupHints : Array Nat)
  | addRat (id : Nat) (c : β) (pivot : Literal α) (rupHints : Array Nat) (ratHints : Array (Nat × Array (Nat)))
  | del (ids : Array Nat)
deriving Inhabited, BEq, Repr

def Action.toString [ToString β] [ToString α] : Action β α → String
  | .addEmpty id rup => s!"addEmpty (id: {id}) (hints: {rup})"
  | .addRup id c rup => s!"addRup {c} (id : {id}) (hints: {rup})"
  | .addRat id c l rup rat => s!"addRat {c} (id: {id}) (pivot: {l}) (rup hints: {rup}) (rat hints: {rat})"
  | .del ids => s!"del {ids}"

instance [ToString β] [ToString α] : ToString (Action β α) := ⟨Action.toString⟩

/--
`Action` where variables are (positive) `Nat`, clauses are arrays of `Int`, and ids are `Nat`.
This Action type is meant to be a convenient target for parsing LRAT proofs.
-/
abbrev IntAction : Type := Action (Array Int) Nat


end LRAT
end Std.Tactic.BVDecide
