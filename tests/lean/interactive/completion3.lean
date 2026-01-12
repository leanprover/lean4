structure S where
  x : Nat
  y : String
  b : Bool

def f (s : S) : Nat :=
  let rec foo (s : S) :=
    if s. then 1 else 2
       --^ completion
  foo s

def g1 (s : S) : Nat × Nat :=
  (s. )
   --^ completion

def g2 (s : S) : Nat × Nat :=
  (s.
   --^ completion

def g3 (s : S) : Nat × Nat :=
  (s. , 1, 2)
   --^ completion
