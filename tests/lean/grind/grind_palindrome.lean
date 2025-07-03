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

-- This give the more natural proof that we'd like to give in `tests/run/grind_palindrome2.lean`,
-- but in which `grind` currently fails.

theorem checkPalin1_correct' : checkPalin1 xs = true ↔ IsPalindrome xs := by
  unfold checkPalin1
  suffices ∀ i, checkPalin1.go xs i = true ↔ ∀ j, i ≤ j → (_ : j < xs.size - i) → xs[j] = xs[xs.size - 1 - j] by
    grind [IsPalindrome]
  intro i
  fun_induction checkPalin1.go
  · grind (splits := 14)
    -- fails, but it would be nice to succeed! The key observations are:
    -- [eqc] True propositions ▼
    --   [prop] ∀ (a : Nat) (b : a + 1 ≤ xs.toList.length - x), a + 1 ≤ x ∨ xs[a] = xs[xs.toList.length - (a + 1)]
    -- [eqc] False propositions ▼
    --   [prop] xs[x] = xs[xs.toList.length - (x + 1)]
    -- Instantiating the `∀` with `a := x`, we can then easily prove `a + 1 ≤ xs.toList.length - x` and
    -- prove that it's not the case that `a + 1 ≤ x`, so we get `xs[x] = xs[xs.toList.length - (x + 1)]`,
    -- which is false.
  · grind
    -- The same argument should apply here.
  · grind
