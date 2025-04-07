/-
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Clune
-/
prelude
import Std.Tactic.BVDecide.LRAT.Actions
import Std.Tactic.BVDecide.LRAT.Internal.Clause

namespace Std.Tactic.BVDecide

namespace LRAT
namespace Internal

open Std.Sat

/--
`Action` where variables have type `PosFin n`, clauses are `DefaultClause`, and ids are `Nat`.
This Action type is meant to be usable for verifying LRAT proofs that operate on default formulas.
-/
abbrev DefaultClauseAction (n : Nat) : Type := Action (DefaultClause n) (PosFin n)

/--
A predicate for Actions that ensures that the pivot of a clause is always included in the clause.
In the LRAT format, the clause's pivot is always its first literal. However, from an interface
perspective, it is awkward to require that all `Clause` implementations preserve the ordering of
their literals. It is also awkward to have the pivot in the `addRat` action not included in the
clause itself, since then the pivot would need to be readded to the clause when it is added to the
formula. So to avoid imposing awkward constraints on the `Clause` interface, and to avoid requiring
`Formula` implementations to add pivots to the clauses provided by the `addRat` action, we use this
predicate to indicate that the pivot provided by the `addRat` action is indeed in the provided
clause.
-/
def WellFormedAction [Clause α β] : Action β α → Prop
  -- Note that `Limplies α p c` is equivalent to `p ∈ toList c` by `limplies_iff_mem` in CNF.lean
  | .addRat _ c p _ _ => Limplies α p c
  | _ => True

@[inline]
def natLiteralToPosFinLiteral {n : Nat} (x : Literal Nat) : Option (Literal (PosFin n)) := do
  if h : x.1 < n ∧ x.1 ≠ 0 then
    some (⟨x.1, ⟨Nat.zero_lt_of_ne_zero h.right, h.left⟩⟩, x.2)
  else
    none

@[inline]
def intToLiteral {n : Nat} (x : Int) : Option (Literal (PosFin n)) := do
  if h1 : x.natAbs < n ∧ x ≠ 0 then
    if h2 : x > 0 then
      some (⟨x.natAbs, ⟨by omega, h1.left⟩⟩, true)
    else
      some (⟨x.natAbs, ⟨by omega, h1.left⟩⟩, false)
  else
    none

/--
Since `IntAction` is a convenient parsing target and `DefaultClauseAction` is a useful Action type
for working with default clauses, an expected workflow pattern is to parse an external LRAT proof
into a list of `IntAction`s, and then use this function to convert that list of `IntAction`s to
`DefaultClauseAction`s.

This function returns an `Option` type so that `none` can be returned if converting from the
`IntAction` to `DefaultClauseAction` fails. This can occur if any of the literals in the `IntAction`
are 0 or ≥ n.
-/
def intActionToDefaultClauseAction (n : Nat) : IntAction → Option (DefaultClauseAction n)
  | .addEmpty cId rupHints => some <| .addEmpty cId rupHints
  | .addRup cId c rupHints => do
    let c ← c.mapM intToLiteral
    let c ← Clause.ofArray c
    return .addRup cId c rupHints
  | .addRat cId c pivot rupHints ratHints => do
    let pivot ← natLiteralToPosFinLiteral pivot
    let c ← c.mapM intToLiteral
    let c ← Clause.ofArray c
    return .addRat cId c pivot rupHints ratHints
  | .del ids => return .del ids


end Internal
end LRAT

end Std.Tactic.BVDecide
