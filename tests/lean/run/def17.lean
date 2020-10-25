

def mk (a : Nat) : Nat → List Nat
| 0   => []
| n+1 => a :: mk a n

def sum : List Nat → Nat → Nat
| [],    r => r
| n::ns, r => sum ns (r + n)

def loop1 : Nat → Nat → Nat
| s, 0   => s
| s, n+1 => loop1 (s + (sum (mk 1 1000000) 0)) n

def loop2 : Nat → Nat → Nat
| 0,   s => s
| n+1, s => loop2 n (s + (sum (mk 1 1000000) 0))

def expensive (n : Nat) : Nat :=
100000000000000 - 100000000000000

def foo : Nat → Nat
| n => expensive n

def bla : Nat → Nat
| 100 => expensive 0
| _   => expensive 1
