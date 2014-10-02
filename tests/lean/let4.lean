import data.num


constant f : num → num → num → num

check
  let a := 10,
      b := 10,
      c := 10
  in f a b (f a 10 c)

check
  let a := 10,
      b := let c := 10 in f a c (f a a (f 10 a c)),
      d := 10,
      e := f (f 10 10 d) (f d 10 10) a
  in f a b (f e d 10)
