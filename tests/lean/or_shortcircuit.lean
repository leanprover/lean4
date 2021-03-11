@[noinline] def c1 (x : Nat) : Bool :=
  dbg_trace "executed c1"
  x == 0

@[noinline] def c2 (x : Nat) : Bool :=
  dbg_trace "executed c2"
  x == 0

@[noinline] def c3 (x : Nat) : Bool :=
  dbg_trace "executed c3"
  x > 0

@[noinline] def f (x : Nat) := x + 1

def tst (x : Nat) : Nat := do
  let x := if !c1 x || (!c2 x && c3 x) then f x else f (x+2)
  match x with
  | 0   => f (x+1)
  | y+1 => f (y+3)

#eval tst 10
