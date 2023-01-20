import Lean.Parser.Module

def main : List String → IO Unit
| [fname, n] => do
  let env ← Lean.mkEmptyEnvironment
  for _ in [0:n.toNat!] do
    discard $ Lean.Parser.testParseFile env fname
| _    => throw $ IO.userError "give file"
