import Lean

set_option trace.compiler.result true
#eval Lean.Compiler.compile #[``Lean.Elab.Deriving.Ord.mkMatch.mkAlts]
