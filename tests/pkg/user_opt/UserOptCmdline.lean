import UserOpt.Opts

/-! Test setting user options from lakefile. -/

open Lean

def tst2 : MetaM Unit := do
  assert! myBoolOpt.get (← getOptions)
  assert! myNatOpt.get (← getOptions) == 4
  pure ()

#eval tst2
