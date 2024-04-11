import Lean.Hygiene
open Lean

set_option trace.compiler.result true
--set_option trace.compiler.ir.result true

-- The following function should not allocate any closures,
-- nor any heap object that doesn't appear in the result:
def foo (n : Nat) : Syntax.Term :=
  Unhygienic.run `(a + $(quote n))
