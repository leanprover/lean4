module

public meta import Lean

/-! Binary size should be independent of `meta` import closure. -/

elab "mk_str" : term =>
  return Lean.mkStrLit "world!"

public def main : IO Unit :=
  IO.println ("Hello, " ++ mk_str)
