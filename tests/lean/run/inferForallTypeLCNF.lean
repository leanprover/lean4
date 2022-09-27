import Lean

variable {U V}

def f : (U → V) → (U → U) := sorry

#eval Lean.Compiler.compile #[``f]
