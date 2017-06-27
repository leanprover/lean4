def expensive (n : ℕ) : ℕ := 100000000000000 - 100000000000000

def foo : ℕ → ℕ | n :=
expensive n

#print foo
#print foo._main
