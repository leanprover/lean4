open nat
example : ℕ → ℕ → Prop
| 0 0               := true
| (succ n) 0        := false
| 0 (succ m)        := false
| (succ n) (succ m) := this n m
