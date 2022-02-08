import UserOpt.Opts

open Lean

def tst1 : MetaM Unit := do
  assert! !(myBoolOpt.get (← getOptions))
  assert! myNatOpt.get (← getOptions) == 100
  pure ()

#eval tst1

set_option myBoolOpt true
set_option myNatOpt 4

def tst2 : MetaM Unit := do
  assert! myBoolOpt.get (← getOptions)
  assert! myNatOpt.get (← getOptions) == 4
  pure ()

#eval tst2
