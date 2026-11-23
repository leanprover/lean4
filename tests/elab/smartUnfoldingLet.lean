module

/-!
Smart unfolding checks matches in `let` values and preserves dependencies between
consecutive `let` and `have` declarations.
-/

private def throughLets : Nat → Nat
  | 0 => 0
  | n+1 =>
    let t := match n with | 0 => 7 | k+1 => throughLets k
    let x : Fin (t+1) := ⟨t, Nat.lt_succ_self t⟩
    have y := x.val
    y

example (P : Nat → Prop) (n : Nat) (h : P (throughLets (n+1))) : P (throughLets (n+1)) := by
  fail_if_success dsimp (config := { autoUnfold := true }) only
  exact h

example (P : Nat → Prop) (k : Nat) (h : P (throughLets k)) : P (throughLets (k+2)) := by
  dsimp (config := { autoUnfold := true }) only
  guard_target =ₛ P (throughLets k)
  exact h
