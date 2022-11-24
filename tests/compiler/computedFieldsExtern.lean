inductive Exp
  | var (i : Nat)
  | app (a b : Exp)
with
  @[computed_field]
  hash : Exp → UInt64
    | .var i => Hashable.hash i
    | .app a b => a.hash + b.hash

def main : IO Unit := do
  -- should be 30 + 3*40 = 150
  IO.println <| Exp.hash (.app (.var 10) (.var 20))
