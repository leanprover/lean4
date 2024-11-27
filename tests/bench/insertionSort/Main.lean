set_option linter.unusedVariables false

abbrev Elem := UInt32

def badRand (seed : Elem) : Elem :=
seed * 1664525 + 1013904223

def mkRandomArray : Nat → Elem → Array Elem → Array Elem
| 0,   seed, as => as
| i+1, seed, as => mkRandomArray i (badRand seed) (as.push seed)

def main (args : List String) : IO UInt32 := do
  let a := mkRandomArray 20000 0 (Array.mkEmpty 20000)
  IO.println (a.insertionSort (· < ·)).size
  return 0
