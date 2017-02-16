def mk (a : nat) : nat → list nat
| 0     := []
| (nat.succ n) := a :: mk n

def Sum : list nat → nat → nat
| []      r := r
| (n::ns) r := Sum ns (r + n)

def loop1 : nat → nat → nat
| s 0            := s
| s (nat.succ n) := loop1 (s + (Sum (mk 1 1000000) 0)) n

def loop2 : nat → nat → nat
| 0            s := s
| (nat.succ n) s := loop2 n (s + (Sum (mk 1 1000000) 0))
