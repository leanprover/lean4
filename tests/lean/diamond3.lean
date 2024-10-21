structure A where
  x : Nat := 0
  y : Nat := 0
  f : Nat → Nat := (· + 10)

structure B extends A where
  z : Nat

structure C extends A where
  w : Nat

set_option structure.diamondWarning false

structure D extends B, C where
  a : Nat

#print D.toC
