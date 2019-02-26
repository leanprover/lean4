@[reducible] def map : Type := rbmap nat bool (<)

def mk_map_aux : nat → map → map
| 0 m := m
| (n+1) m := mk_map_aux n (m.insert n (n % 10 = 0))

def mk_map (n : nat) :=
mk_map_aux n (mk_rbmap nat bool (<))

def main (xs : list string) : io uint32 :=
let m := mk_map xs.head.to_nat in
let v := rbmap.fold (λ (k : nat) (v : bool) (r : nat), if v then r + 1 else r) m 0 in
io.println' (to_string v) *>
pure 0
