import Std.Data.PersistentArray

def check [BEq α] (as : List α) : Bool :=
  as.toPersistentArray.foldr (.::.) [] == as

def tst1 : IO Unit := do
  assert! check [1, 2, 3]
  assert! check ([] : List Nat)
  assert! check (List.iota 17)
  assert! check (List.iota 533)
  assert! check (List.iota 1000)
  assert! check (List.iota 2600)
  IO.println "done"

#eval tst1
