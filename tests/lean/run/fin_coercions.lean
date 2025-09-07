set_option pp.mvars false

-- We first verify that there is no global coercion from `Nat` to `Fin n`.
-- Such a coercion would frequently introduce unexpected modular arithmetic.

/--
error: Type mismatch
  n
has type
  Nat
but is expected to have type
  Fin 3
---
info: fun n => sorry : (n : Nat) → ?_ n
-/
#guard_msgs in #check fun (n : Nat) => (n : Fin 3)

-- This instance is available via `open Fin.NatCast in ...`

section

open Fin.NatCast

variable (m : Nat) (n : Fin 3)
/-- info: n < ↑m : Prop -/
#guard_msgs in #check n < m

end

example (x : Fin (n + 1)) (h : x < n) : Fin (n + 1) := x.succ.castLT (by simp [h])
