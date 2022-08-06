import Lean

open Lean Compiler Meta

set_option trace.Meta.debug true
set_option pp.funBinderTypes true
#eval Compiler.compile #[``List.map]
