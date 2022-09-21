import Lean

set_option trace.Compiler.result true
#eval Lean.Compiler.compile #[``Lean.Elab.Deriving.Ord.mkMatch.mkAlts]
