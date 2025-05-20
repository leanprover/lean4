set_option grind.warning false

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

example (xs : Array Nat) (w : xs.reverse = xs) (j : Nat) (hj : 0 ≤ j) (hj' : j < xs.size / 2) :
    xs[j] = xs[xs.size - 1 - j] := by
  grind

attribute [grind ext] Array.ext -- TODO: should we mark it by default?

theorem checkPalin1_correct' : checkPalin1 xs = true ↔ IsPalindrome xs := by
  unfold checkPalin1
  suffices ∀ i, checkPalin1.go xs i = true ↔ ∀ j, i ≤ j → (_ : j < xs.size / 2) → xs[j] = xs[xs.size - 1 - j] by
    grind [IsPalindrome]
  intro i
  fun_induction checkPalin1.go <;> grind
