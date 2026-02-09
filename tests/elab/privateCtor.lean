structure Foo where
  private mk ::
    num : Int
    den : Nat := 1

def Foo.normalize (a : Foo) : Foo :=
  let n := Nat.gcd a.num.natAbs a.den
  if n == 1 then a else { num := a.num / n, den := a.den / n }
