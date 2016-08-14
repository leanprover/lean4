open nat
attribute [pattern] lt.base
attribute [pattern] lt.step

theorem lt_succ : ∀ {a b : nat}, a < b → succ a < succ b
| lt_succ (lt.base a)  := lt.base (succ a)
| lt_succ (lt.step h)  := lt.step (lt_succ h)
