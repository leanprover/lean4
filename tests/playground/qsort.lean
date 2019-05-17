abbreviation Elem := UInt32

def badRand (seed : Elem) : Elem :=
seed * 1664525 + 1013904223

def mkRandomArray : Nat → Elem → Array Elem → Array Elem
| 0     seed as := as
| (i+1) seed as := mkRandomArray i (badRand seed) (as.push seed)

partial def checkSortedAux (a : Array Elem) : Nat → IO Unit
| i :=
  if i < a.size - 1 then do
    unless (a.get i <= a.get (i+1)) $ throw (IO.userError "array is not sorted"),
    checkSortedAux (i+1)
  else
    pure ()

def main (xs : List String) : IO Unit :=
do
let n := xs.head.toNat,
n.mfor $ λ _,
n.mfor $ λ i, do
  let xs := mkRandomArray i (UInt32.ofNat i) Array.empty,
  let xs := xs.qsort (λ a b, a < b),
  --IO.println xs,
  checkSortedAux xs 0
