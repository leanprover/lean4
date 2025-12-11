module
def IsPalindrome (xs : Array Nat) : Prop := xs.reverse = xs

def checkPalin1 (xs : Array Nat) : Bool :=
  go 0
where
  go  (i : Nat) :=
    if h : i < xs.size / 2 then
      if xs[i] = xs[xs.size - 1 - i] then
        go (i + 1)
      else
        false
    else
      true

-- This works nicely, but there is some human assistance here:
-- on the right hand side of the `suffices` we've asserted it's enough to check up to `j < xs.size / 2`
-- while the "natural" statement would be all the way to `j < xs.size - i`.
theorem checkPalin1_correct : checkPalin1 xs = true ↔ IsPalindrome xs := by
  unfold checkPalin1
  suffices ∀ i, checkPalin1.go xs i = true ↔ ∀ j, i ≤ j → (_ : j < xs.size / 2) → xs[j] = xs[xs.size - 1 - j] by
    grind [IsPalindrome]
  intro i
  fun_induction checkPalin1.go with grind
