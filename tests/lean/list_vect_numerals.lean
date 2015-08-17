import data.list data.examples.vector data.real
open nat int real list vector

variables n m : nat
variables i j : int
variables x y : real
variables v   : vector real 3

check [n, m]     -- list nat
check [n, i]     -- list int
check [i, n]     -- list int
check [i, n, x]  -- list real

check ([i, n, x, y] : vector _ _) -- vector of reals
check (tail [i, n, x, y] = v)

check [i, n, x] = v
set_option pp.notation false
set_option pp.full_names true
check [i, n, x] = v
check (tail [i, n, x, y] = v)
