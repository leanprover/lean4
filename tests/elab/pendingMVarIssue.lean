structure Point where
  x : Nat
  y : Nat

def Point.compute1 (p : Point) : Point :=
  let p := { p with x := 1 }
  let p := { p with y := 0 }
  if (p.x - p.y) > p.x then p else p

def Point.compute2 (p : Point) : Point :=
  let q := { p with x := 1 }
  let r := { q with y := 0 }
  if (r.x - r.y) > r.x then r else r
