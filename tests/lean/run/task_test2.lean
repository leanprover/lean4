--

def run1 (i : Nat) (n : Nat) (xs : List Nat) : Nat :=
n.repeat (fun r =>
  dbg_trace ">> [{i}] {r}";
  xs.foldl (fun a b => a + b) r)
0

def tst (n : Nat) : IO UInt32 :=
let ys := (List.replicate n 1);
let ts : List (Task Nat) := (List.iota 10).map (fun i => Task.spawn fun _ => run1 (i+1) n ys);
let ns : List Nat := ts.map Task.get;
IO.println (">> " ++ toString ns) *>
pure 0

/--
info: >> [100, 100, 100, 100, 100, 100, 100, 100, 100, 100]
---
info: 0
-/
#guard_msgs in
#eval tst 10
