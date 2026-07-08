import Lean

variable {U V}

def f : (U → V) → (U → U) := sorry

run_meta Lean.Compiler.compile #[``f]
