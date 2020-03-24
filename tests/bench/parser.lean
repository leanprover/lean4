import Init.Lean.Parser

def main : List String → IO Unit
| [fname, n] => do
  env ← Lean.mkEmptyEnvironment;
  n.toNat!.forM $ fun _ =>
    Lean.Parser.parseFile env fname *> pure ();
  pure ()
| _    => throw $ IO.userError "give file"
