/-!
`cases` closes a goal with a hypothesis that equates two different `String` literals, also when
the literals are nested in constructor applications.
-/

example (h : "a" = "b") : False := by
  cases h

example (h : "a" = "ab") : False := by
  cases h

example (n : Nat) (h : (1, "c") = (n, "b")) : False := by
  cases h

example (h : some "a" = some "") : 1 = 2 := by
  cases h

example (x : Nat) (h : [("a", x)] = [("b", 0)]) : False := by
  cases h

/-! Equal literals are not a contradiction: the other equalities are still used. -/

example (n : Nat) (h : (1, "c") = (n, "c")) : n = 1 := by
  cases h
  rfl

example (s : String) (h : (s, "c") = ("b", "c")) : s = "b" := by
  cases h
  rfl
