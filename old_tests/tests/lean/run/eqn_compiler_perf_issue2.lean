def expensive (n : ℕ) : ℕ := 100000000000000 - 100000000000000

def foo : ℕ → ℕ | n :=
expensive n

#print foo
#print foo._main

def bla : ℕ → ℕ
| 100 := expensive 0
| _   := expensive 1
