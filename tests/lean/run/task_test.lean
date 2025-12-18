

def g (x : Nat) : Nat :=
dbgTrace ("g: " ++ toString x) $ fun _ =>
  x + 1

def f1 (x : Nat) : Nat :=
dbgSleep 1000 $ fun _ =>
dbgTrace ("f1: " ++ toString x) $ fun _ =>
  g (x + 1)

def f2 (x : Nat) : Nat :=
dbgSleep 100 $ fun _ =>
dbgTrace ("f2: " ++ toString x) $ fun  _ =>
  g x

def tst (n : Nat) : IO UInt32 :=
let t1 := Task.spawn fun _ => f1 n;
let t2 := Task.spawn fun _ => f2 n;
dbgSleep 1000 $ fun _ =>
IO.println (toString t1.get ++ " " ++ toString t2.get) *>
pure 0

/--
info: 12 11
---
info: 0
-/
#guard_msgs in
#eval tst 10
