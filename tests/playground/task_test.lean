def g (x : Nat) : Nat :=
dbgTrace ("g: " ++ toString x) $ λ _,
  x + 1

def f1 (x : Nat) : Nat :=
dbgSleep 1000 $ λ _,
dbgTrace ("f1: " ++ toString x) $ λ _,
  g (x + 1)

def f2 (x : Nat) : Nat :=
dbgSleep 100 $ λ _,
dbgTrace ("f2: " ++ toString x) $ λ _,
  g x

def main (xs : List String) : IO UInt32 :=
let t1 := Task.mk $ (λ _, f1 xs.head.toNat) in
let t2 := Task.mk $ (λ _, f2 xs.head.toNat) in
dbgSleep 1000 $ λ _,
IO.println (toString t1.get ++ " " ++ toString t2.get) *>
pure 0
