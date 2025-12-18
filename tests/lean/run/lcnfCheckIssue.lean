import Lean

abbrev Sequence (α : Type) := List α

def bigop (init : β) (seq : Sequence α) (op : β → β → β) (f : α → Bool × β) : β := Id.run do
  let mut result := init
  for a in seq do
    let (ok, b) := f a
    if ok then
      result := op result b
  return result

set_option trace.Compiler.result true
run_meta Lean.Compiler.compile #[``bigop]
