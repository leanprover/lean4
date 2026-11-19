structure A where
  x : Nat

structure B extends A where
  x := _ -- should be error

structure C extends A where
  x := _ + 1 -- should be error
