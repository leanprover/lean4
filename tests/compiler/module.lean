module

public meta import Lean

elab "mk_str" : term =>
  return Lean.mkStrLit "elab'd"

public def main : IO Unit :=
  IO.println mk_str
