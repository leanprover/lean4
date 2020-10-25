import Lean.Parser

def main : List String → IO Unit
| [fname, n] => do
  let env ← Lean.mkEmptyEnvironment
  for _ in [0:n.toNat!] do
    discard $ Lean.Parser.parseFile env fname
| _    => throw $ IO.userError "give file"
