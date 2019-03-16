def g (x : nat) : nat :=
dbg_trace ("g: " ++ to_string x) $ λ _,
  x + 1

def f1 (x : nat) : nat :=
dbg_sleep 1000 $ λ _,
dbg_trace ("f1: " ++ to_string x) $ λ _,
  g (x + 1)

def f2 (x : nat) : nat :=
dbg_sleep 100 $ λ _,
dbg_trace ("f2: " ++ to_string x) $ λ _,
  g x

def main (xs : list string) : io uint32 :=
let t1 := task.mk $ (λ _, f1 xs.head.to_nat) in
let t2 := task.mk $ (λ _, f2 xs.head.to_nat) in
dbg_sleep 1000 $ λ _,
io.println (to_string t1.get ++ " " ++ to_string t2.get) *>
pure 0
