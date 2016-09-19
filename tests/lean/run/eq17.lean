set_option new_elaborator true
open nat
attribute [pattern] lt.base
attribute [pattern] lt.step

definition lt_of_succ {a : nat} : ∀ {b : nat}, succ a < b → a < b
| .(succ (succ a)) (lt.base .(succ a))       := nat.lt_trans (lt.base a) (lt.base (succ a))
| .(succ b)        (@lt.step .(succ a) b h)  := lt.step  (lt_of_succ h)
