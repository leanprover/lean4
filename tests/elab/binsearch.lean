partial def mkAssocArray : Nat → Array (Nat × Bool) → Array (Nat × Bool)
| 0,   as => as
| i+1, as  => mkAssocArray i (as.push (i, i % 2 == 0))

def tst (n : Nat) : IO Unit :=
do
let as := mkAssocArray n Array.empty;
IO.println as;
let as := as.qsort (fun a b => a.1 < b.1);
for i in [:2*n] do
  let entry := as.binSearch (i, false) (fun a b => a.1 < b.1);
  IO.println (">> " ++ toString i ++ " ==> " ++ toString entry)

#eval tst 10
