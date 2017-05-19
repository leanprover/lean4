/- unknown identifiers -/

def f1 : ℕ → ℕ
| 42 := 9000
| arg := ag

#eval f1 42 -- OK (prints 9000)

/- incomplete structure instances -/

def f2 : ℕ × ℕ := { fst := 9000, sn}

#reduce f2.fst -- OK (prints 9000)

/- incomplete if-then-else -/

def f3 (x : ℕ) : ℕ :=
(if x ≥ 42 then 9000)
                 -- ^ missing else reported here

#eval f3 42 -- OK (prints 9000)