import Lean

def bar : ReaderM Unit Unit :=
  if true then
    match true with
    | true  => pure ()
    | false => pure ()
  else
    pure ()

set_option trace.compiler true
#eval Lean.Compiler.compile #[``bar]
