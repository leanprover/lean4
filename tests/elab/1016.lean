module

inductive t | one | two

example (h : False) : t.one = t.two := by
  simp
  contradiction
