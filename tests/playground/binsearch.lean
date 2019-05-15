def mkAssocArray : Nat → Array (Nat × Bool) → Array (Nat × Bool)
| 0     as := as
| (i+1) as := mkAssocArray i (as.push (i, i % 2 == 0))

def main (xs : List String) : IO Unit :=
do
let n  := xs.head.toNat,
let as := mkAssocArray n Array.empty,
let as := as.qsort (λ a b, a.1 < b.1),
(2*n).mfor $ λ i, do
  let entry := as.binSearch (i, false) (λ a b, a.1 < b.1),
  IO.println (">> " ++ toString i ++ " ==> " ++ toString entry)
