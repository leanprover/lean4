inductive Palindrome : List α → Prop where
  | nil      : Palindrome []
  | single   : (a : α) → Palindrome [a]
  | sandwish : (a : α) → Palindrome as → Palindrome ([a] ++ as ++ [a])

theorem palindrome_reverse (h : Palindrome as) : Palindrome as.reverse :=
  match h with
  | .nil => .nil
  | .single a => Palindrome.single a
                --^ textDocument/hover
  | .sandwish a h => by simp; exact .sandwish _ (palindrome_reverse h)
