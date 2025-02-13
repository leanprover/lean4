/--
error: type mismatch
  Nat
has type
  Type : Type 1
but is expected to have type
  Lean.PremiseSelection.Selector : Type
---
error: Failed to elaborate Nat as a `MVarId → Config → MetaM (Array Suggestion)`.
-/
#guard_msgs in
set_premise_selector Nat

/--
error: No premise selector registered. (Note the Lean does not provide a default premise selector, these must be installed by a downstream library.)
-/
#guard_msgs in
example : True := by
  suggest_premises
  trivial

set_premise_selector (fun _ _ => pure #[])

/-- info: Premise suggestions: [] -/
#guard_msgs in
example : True := by
  suggest_premises
  trivial

set_premise_selector Lean.PremiseSelection.random ⟨1,1⟩

-- This would be an extremely fragile test (select 10 random constants!)
-- so remove before merging.
/--
info: Premise suggestions: [Lean.Parser.«command_Builtin_dsimproc_decl_(_):=_»._closed_9._cstage2,
 Int.Linear.Expr.toPoly'._closed_2._cstage2,
 Lean.HashSet.numBuckets._rarg,
 Lean.Parser.Tactic.rintroPat.quot._closed_2._cstage2,
 Lean.Parser.Command.declValEqns._closed_1,
 Lean.Parser.Command.printEqns._closed_6._cstage2,
 Lean.Parser._aux_Init_Notation___macroRules_Lean_Parser_commandSeal___1._closed_7._cstage2,
 _private.Init.Data.Array.QSort.0.Array.qpartition.loop._unary.proof_5,
 Nat.instMax._boxed,
 Lean.PrettyPrinter.Delaborator.delabLit._closed_1._cstage2]
-/
#guard_msgs in
example : True := by
  suggest_premises
  trivial
