open nat

theorem lt_trans : ∀ {a b c : nat}, a < b → b < c → a < c
| lt_trans h  (lt.base _)   := lt.step h
| lt_trans h₁ (lt.step h₂)  := lt.step (lt_trans h₁ h₂)

theorem lt_succ : ∀ {a b : nat}, a < b → succ a < succ b
| lt_succ (lt.base a)  := lt.base (succ a)
| lt_succ (lt.step h)  := lt.step (lt_succ h)
