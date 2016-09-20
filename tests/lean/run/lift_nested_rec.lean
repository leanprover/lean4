
definition f : nat → (nat × nat) → nat
| 0      m := m.1
| (n+1)  m :=
  match m with
  | (a, b) := (f n (b, a + 1)) + (f n (a, b))
  end

check @f._main.equations.eqn_1
check @f._main.equations.eqn_2
check @f._match_1.equations.eqn_1
