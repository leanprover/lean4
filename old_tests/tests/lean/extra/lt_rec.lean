open nat

set_option pp.implicit true
set_option pp.notation false

definition lt_trans : ∀ {a b c : nat}, a < b → b < c → a < c,
lt_trans h  (lt.base _)   := lt.step h,
lt_trans h₁ (lt.step h₂)  := lt.step (lt_trans h₁ h₂)

definition lt_succ : ∀ {a b : nat}, a < b → succ a < succ b,
lt_succ (lt.base a)  := lt.base (succ a),
lt_succ (lt.step h)  := lt.step (lt_succ h)

definition lt_of_succ : ∀ {a b : nat}, succ a < b → a < b,
lt_of_succ (lt.base (succ a)) := lt.trans (lt.base a) (lt.base (succ a)),
lt_of_succ (lt.step h₂)       := lt.step (lt_of_succ h₂)
