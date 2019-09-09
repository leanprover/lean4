def run1 (i : Nat) (n : Nat) (xs : List Nat) : Nat :=
n.repeat (fun r =>
  let s := (">> [" ++ toString i ++ "] " ++ toString r);
  xs.foldl (fun a b => a + b) (r + s.length))
0

def main (xs : List String) : IO UInt32 :=
let ys := (List.replicate xs.head.toNat 1);
let ts : List (Task Nat) := (List.iota 10).map (fun i => Task.mk $ fun _ => run1 (i+1) xs.head.toNat ys);
let ns : List Nat := ts.map Task.get;
IO.println (">> " ++ toString ns) *>
pure 0
