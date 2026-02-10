set_option debug.skipKernelTC true
def go (pat : ByteArray) (stackPos : Nat) (hst : stackPos < pat.size) (guess : Nat) (hg : guess < stackPos) : { n : Nat // n ≤ stackPos } :=
    if pat[guess] = pat[stackPos] then
      ⟨guess + 1, by sorry⟩
    else if h : guess = 0 then
      ⟨0, by simp⟩
    else
      have : (go pat stackPos hst (guess - 1) (by omega)) < guess := by
        sorry
      have : guess - 1 < stackPos := by omega
      go pat stackPos hst (go pat stackPos hst (guess - 1) (by assumption)) (by grind)
termination_by guess
decreasing_by all_goals sorry
