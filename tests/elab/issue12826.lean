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
error: Bug in a `do` elaborator. The free variable `bad_fvar` is not in scope in
  fun __r => bad_fvar
-/
#guard_msgs in
def testFn : IO Unit := do
  if true then pure () else pure () -- uses `withDuplicableCont`
  test -- produces a term with a free variable that is not in scope

set_option pp.mvars false
