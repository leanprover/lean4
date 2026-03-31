structure A where
  x : Nat

structure B extends A where
  x := 1
  x := 2 -- Error
