def foo (pat : ByteArray) (stackPos : Nat) (hst : stackPos < pat.size) : { n : Nat // n ≤ stackPos } :=
  if h : stackPos = 0 then
    ⟨0, by simp⟩
  else
    go (stackPos - 1) (by omega)
termination_by stackPos
where
  go (guess : Nat) (hg : guess < stackPos) : { n : Nat // n ≤ stackPos } :=
    if pat[guess] = pat[stackPos] then
      ⟨guess + 1, by omega⟩
    else if h : guess = 0 then
      ⟨0, by simp⟩
    else
      have : (foo pat (guess - 1) (by omega)) < guess := by
        have := (foo pat (guess - 1) (by omega)).property
        omega
      go (foo pat (guess - 1) (by omega)) (by omega)
  termination_by guess
