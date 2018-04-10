axiom DivS (x : nat) : x ≠ 0 → x / x = 1

open tactic

example (x : nat) (h : x ≠ 0) : x / x = 1 :=
begin
  simp[DivS, h]
end

example (x : nat) (h : x ≠ 0) : x / x = 1 :=
begin
  fail_if_success {simp [DivS]},
  simp [DivS] {discharger := assumption}
end

constant f : nat → nat → nat
axiom flemma : ∀ a b, b ≠ 0 → a ≠ 0 → f a b = 0

example (x : nat) (h : x ≠ 0) : f 1 x = 0 :=
begin
  simp [flemma] {discharger := trace "subgoal" >> trace_state >> (assumption <|> comp_val)}
end
