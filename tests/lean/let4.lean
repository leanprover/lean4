--

constant f : num → num → num → num

#check
  let a : num := 10,
      b : num := 10,
      c : num := 10
  in f a b (f a 10 c)

#check
  let a : num := 10,
      b : num := let c : num := 10 in f a c (f a a (f 10 a c)),
      d : num := 10,
      e : num := f (f 10 10 d) (f d 10 10) a
  in f a b (f e d 10)
