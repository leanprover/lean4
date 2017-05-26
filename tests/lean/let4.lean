--

constant f : nat → nat → nat → nat

#check
  let a : nat := 10,
      b : nat := 10,
      c : nat := 10
  in f a b (f a 10 c)

#check
  let a : nat := 10,
      b : nat := let c : nat := 10 in f a c (f a a (f 10 a c)),
      d : nat := 10,
      e : nat := f (f 10 10 d) (f d 10 10) a
  in f a b (f e d 10)
