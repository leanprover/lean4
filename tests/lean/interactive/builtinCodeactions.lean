/-- Must not introduce line break between `at` and `h` -/
example {a b c d : Nat} (h : a = b)
    (AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA : b = c)
    (aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : c = d) :
    a = b := by
  simp? [AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA, aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa] at h
  --^ codeAction
