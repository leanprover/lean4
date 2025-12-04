structure X
def X.x (_ : X) : BaseIO Bool := sorry

set_option trace.Elab.info true
def f : IO Unit := do
  let _ ← ([] : List X).findM? fun p => p.x
