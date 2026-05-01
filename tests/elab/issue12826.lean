import Lean

syntax (name := testElem) "test" : doElem

open Lean Elab Do
@[doElem_elab testElem]
def elabTestElem : DoElab := fun _stx _dec => do
  return .fvar ⟨`bad_fvar⟩

@[doElem_control_info testElem]
def controlInfoTestElem : ControlInfoHandler := fun _stx => do
  return .pure

set_option backward.do.legacy false

/--
error: Bug in a `do` elaborator. Failed to assign join point RHS
  fun __r => bad_fvar
to metavariable
⊢ Unit → IO Unit
-/
#guard_msgs in
def testFn : IO Unit := do
  if true then pure () else pure () -- uses `withDuplicableCont`
  test -- produces a term that `checkedAssign` will reject

set_option pp.mvars false
