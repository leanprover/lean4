import Lean.Parser.Module

/-!
  Test parsing only on a .lean file, which necessarily has to be one that does
  not depend on non-built-in syntax, e.g. `Init.Prelude`. -/

def main : List String → IO Unit
| [fname, n] => do
  let env ← Lean.mkEmptyEnvironment
  for _ in [0:n.toNat!] do
    discard $ Lean.Parser.testParseFile env fname
| _ => throw $ IO.userError "give file and iteration count"
