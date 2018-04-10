def f (n : ℕ) := n.to_string
                --^ "command": "info"
def g (l : list ℕ) := l.all
                       --^ "command": "info"

-- elaborated, not locally inferable
def h : list ℕ → (ℕ → bool) → bool :=
λ l, (l ++ l).all
           --^ "command": "info"

-- not elaborated, locally inferable
def j := (list.nil^.all
                   --^ "command": "info"
