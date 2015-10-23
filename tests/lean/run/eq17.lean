open nat

definition lt_of_succ : ∀ {a b : nat}, succ a < b → a < b
| lt_of_succ (lt.base (succ a)) := nat.lt_trans (lt.base a) (lt.base (succ a))
| lt_of_succ (lt.step h)        := lt.step  (lt_of_succ h)
