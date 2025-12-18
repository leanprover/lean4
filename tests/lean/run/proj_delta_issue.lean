def ack : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ack x 1
  | x+1, y+1 => ack x (ack (x+1) y)

structure S where
  x : Nat
  y : Nat

def f (x : Nat) : S :=
  { x, y := ack 10 20 }

def g (x : Nat) : S :=
  { x, y := ack 20 20 }

example : (f x).1 = (g x).1 :=
  rfl
