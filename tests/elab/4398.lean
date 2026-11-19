example {ι : Type _} (n m : ι) (h : n = m) : m = n := by
  simp only [id h] -- should work

example {ι : Type _} (n m : ι) (h : n = m) : m = n := by
  simp only [h] -- works
