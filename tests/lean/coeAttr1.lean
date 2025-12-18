@[coe] def f (n : Nat) : String :=
  toString n

#check f 10

instance : Coe Nat String where
  coe := f

def g (n : String) := n

#check fun x : Nat => g x
