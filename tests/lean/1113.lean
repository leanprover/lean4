def foo: {n: Nat} → Fin n → Nat
|   0, _ => 0
| n+1, _ => 0

theorem t3 {f: Fin (n+1)}:
  foo f = 0 := by
  dsimp only [←Nat.succ_eq_add_one n] at f -- use `dsimp` to ensure we don't copy `f`
  trace_state
  simp only [←Nat.succ_eq_add_one n, foo]

example {n: Nat} {f: Fin (n+1)}:
  foo f = 0 := by
  revert f
  rw[←Nat.succ_eq_add_one n]
  intro f
  simp only [foo]
