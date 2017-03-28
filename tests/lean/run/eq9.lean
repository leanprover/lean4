open nat
attribute [pattern] lt.base
attribute [pattern] lt.step

theorem lt_succ {a : nat} : ∀ {b : nat}, a < b → succ a < succ b
| .(succ a) (lt.base .(a))       := lt.base (succ a)
| .(succ b) (@lt.step .(a) b h)  := lt.step (lt_succ h)
