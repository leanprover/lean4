import standard unit decidable
using bit unit decidable

variables a b c : bit
variables u v : unit

theorem tst : decidable ((a = b) ∧ (b = c) → ¬ (u = v) ∨ (a = c) → (a = c) ↔ a = '1 ↔ true)

(*
print(get_env():find("tst"):value())
*)
