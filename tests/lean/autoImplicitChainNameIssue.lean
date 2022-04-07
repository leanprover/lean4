inductive Palindrome : List α → Prop where
  | nil      : Palindrome []
  | single   : (a : α) → Palindrome [a]
  | sandwish : (a : α) → Palindrome as → Palindrome ([a] ++ as ++ [a])

theorem palindrome_reverse (h : Palindrome as) : Palindrome as.reverse := by
  induction h with
  | nil => done
  | single a => exact Palindrome.single a
  | sandwish a h ih => simp; exact Palindrome.sandwish _ ih

#check @palindrome_reverse
