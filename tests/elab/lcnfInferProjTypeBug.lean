import Lean

set_option trace.Compiler.result true
run_meta Lean.Compiler.compile #[``Lean.Meta.mapMetaM]
