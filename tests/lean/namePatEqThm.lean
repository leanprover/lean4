@[simp] def iota : Nat → List Nat
  | 0       => []
  | m@(n+1) => m :: iota n

#check iota._eq_1
#check iota._eq_2

@[simp] def f : List Nat → List Nat × List Nat
 | xs@(x :: ys@(y :: [])) => (xs, ys)
 | xs@(x :: ys@(y :: zs)) => f zs
 | _ => ([], [])

#check f._eq_1
#check f._eq_2
#check f._eq_3
