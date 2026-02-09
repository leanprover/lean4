def f (y : Nat) :=
  let x := 1x + y -- Error

structure Point where
 x : Nat
 y : Nat
deriving Repr

def mkPoint1 (a : Nat) : Point where
  x := 1y := a -- Error

def mkPoint2 (a : Nat) : Point where
  x := 1
  y := a

def mkPoint3 (a : Nat) : Point where
  x := 1; y := a

def mkPoint?? (x y : Nat) : Point :=
  { x y }
