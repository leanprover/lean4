set_option backward.do.legacy false
/-! This test case used to trigger an infinite loop in the old `do` elaborator. -/
set_option showPartialSyntaxErrors true
def f : IO Unit := do
  if let
