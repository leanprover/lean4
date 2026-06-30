structure Point where
  x : Nat
  y : Nat
deriving Repr

structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr

def origin : Point :=
  { x := Nat.zero, y := Nat.zero }

def natOrigin : PPoint Nat :=
  { x := Nat.zero, y := Nat.zero }

#eval origin
#eval natOrigin
