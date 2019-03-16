def run1 (i : nat) (n : nat) (xs : list nat) : nat :=
n.repeat (λ _ r,
  dbg_trace (">> [" ++ to_string i ++ "] " ++ to_string r) $ λ _,
  xs.foldl (+) r)
0

def main (xs : list string) : io uint32 :=
let ys := (list.repeat 1 xs.head.to_nat) in
let ts : list (task nat) := (list.iota 10).map (λ i, task.mk $ λ _, run1 (i+1) xs.head.to_nat ys) in
let ns : list nat := ts.map task.get in
io.println (">> " ++ to_string ns) *>
pure 0
