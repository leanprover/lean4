open nat

def f : ℕ → ℕ → ℕ
| 0        b := 0
| (succ n) b := begin cases b with b', exact 0, exact f n b' end
