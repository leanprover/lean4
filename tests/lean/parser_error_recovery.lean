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

/- η-expanded syntax errors -/

def f4 : list ℕ :=
list.map nat.suc []

#eval f4 -- OK (prints [])

/- tactic scripts with syntax errors -/

lemma f5 (x : ℕ) : x+1 = 1+x :=
by {
    simp,
    trace_state, -- OK (no goals)
    simmp,,,