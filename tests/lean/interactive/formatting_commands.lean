structure   Point where
  x :    Nat
  y :    Nat

instance :   ToString Point where
  toString p :=   s!"({p.x}, {p.y})"

def   origin : Point :=  { x := 0,   y := 0 }
--^ formatting
