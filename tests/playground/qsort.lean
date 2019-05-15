def mkRandomArray (max : Nat) : Nat → Array Nat → IO (Array Nat)
| 0     as := pure as
| (i+1) as := do a ← IO.rand 0 max, mkRandomArray i (as.push a)

partial def checkSortedAux (a : Array Nat) : Nat → IO Unit
| i :=
  if i < a.size - 1 then do
    unless (a.get i <= a.get (i+1)) $ throw (IO.userError "array is not sorted"),
    checkSortedAux (i+1)
  else
    pure ()

def test1 (xs : Array Nat) : IO Unit :=
do
let xs := xs.qsort (λ a b, a < b),
IO.println ("sorted array of size: " ++ toString (xs.size))

def main (xs : List String) : IO Unit :=
do
let n    := xs.head.toNat,
let seed := xs.tail.head.toNat,
let m    := xs.tail.tail.head.toNat,
xs ← mkRandomArray m m Array.empty,
timeit "qsort" (test1 xs),
IO.setRandSeed seed,
n.mfor $ λ _,
n.mfor $ λ i, do
  xs ← mkRandomArray (i*2) i Array.empty,
  let xs := xs.qsort (λ a b, a < b),
  IO.println xs,
  checkSortedAux xs 0
