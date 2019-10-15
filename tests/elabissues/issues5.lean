import Init.Data.HashMap

def f (a : HashMap Nat Nat) : HashMap Nat Nat :=
a

def t (as : List Nat) :=
let xs := {};
/- We can't elaborate r.insert at this point because we don't know the type of `r`.
   Our plan is to suspend it by creating a metavariable, and resume later when we have
   more information. -/
let ys := as.foldl (fun r a => r.insert a) xs;
/- After elaborating `f xs`, we learn that `xs` has type `HashMap Nat Nat`. Then,
   we have enough information for resuming the elaboration of `r.insert a` -/
let zs := f xs;
ys
