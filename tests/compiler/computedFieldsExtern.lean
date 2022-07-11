inductive Exp
  | var (i : Nat)
  | app (a b : Exp)
with
  @[computedField, extern c inline "(lean_ctor_get_uint64(#1, lean_ctor_num_objs(#1)*sizeof(void*)) + 40)"]
  hash : Exp → UInt64
    | .var i => Hashable.hash i
    | .app a b => a.hash + b.hash

def main : IO Unit := do
  -- should be 30 + 3*40 = 150
  IO.println <| Exp.hash (.app (.var 10) (.var 20))
