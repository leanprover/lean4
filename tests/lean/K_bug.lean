open eq.ops

inductive Nat : Type :=
zero : Nat,
succ : Nat → Nat

namespace Nat

definition pred (n : Nat) := Nat.rec zero (fun m x, m) n
theorem pred_succ (n : Nat) : pred (succ n) = n := rfl

theorem succ_inj {n m : Nat} (H : succ n = succ m) : n = m
:= calc
    n = pred (succ n) : pred_succ n⁻¹
  ... = pred (succ m) : {H}
  ... = m             : pred_succ m

end Nat
