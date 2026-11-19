inductive Foo (n: Nat)
  | mk: n = 0 → Foo n

example (h: Foo x): x + 1 = 1 := by
  cases h
  subst x
  rfl
