import Lean

open Lean BitVec

open Meta in
def test [ToExpr α] (a : α) : MetaM Unit := do
  let e := toExpr a
  let type ← inferType e
  check e
  logInfo m!"{e} : {type}"

run_meta test (2 : Fin 4)
run_meta test (8 : Fin 5)
run_meta test (300#8)
run_meta test (300#32)
run_meta test (58#8)
run_meta test (20 : UInt8)
run_meta test (30 : UInt16)
run_meta test (40 : UInt32)
run_meta test (50 : UInt64)
run_meta test (60 : USize)
