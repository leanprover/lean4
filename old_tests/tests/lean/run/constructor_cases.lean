example (p q r : Prop) : p → q → r → r ∧ p ∧ q :=
begin
  intros hp hq hr,
  with_cases { repeat { constructor } },
  case left { exact hr },
  case right left { exact hp },
  case right right { exact hq }
end

example (p q r : Prop) : p → q → r → r ∧ p ∧ q :=
begin
  intros hp hq hr,
  with_cases { repeat { constructor } },
  case right left { exact hp },
  case right right { exact hq },
  case left { exact hr }
end

example (p q r : Prop) : p → q → r → r ∧ p ∧ q :=
begin
  intros hp hq hr,
  with_cases { repeat { split } },
  case right left { exact hp },
  case right right { exact hq },
  case left { exact hr }
end

open tactic

example (n : nat) : nat :=
begin
  with_cases { right },
  /- The tactic `right` should not extend the tag since nat.succ has only one argument. -/
  (do t : list name ← get_main_tag, trace t, guard (t.tail = [])),
  case { exact n }
end
