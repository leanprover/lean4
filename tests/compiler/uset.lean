structure Point where
  x : USize
  y : UInt32

@[noinline] def Point.right (p : Point) : Point :=
  { p with x := p.x + 1 }

def main : IO Unit :=
  IO.println (Point.right ⟨0, 0⟩).x
