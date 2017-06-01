meta def loop : nat → nat
| n := loop n

meta def tst : expr := `(loop 1)

#eval tst
