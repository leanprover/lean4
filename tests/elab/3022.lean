def foo : Nat → Nat
  | 0 => 2
  | n + 1 => foo n

example (n : Nat) : foo (n + 1) = 2 := by
  unfold foo      -- should not produce `⊢ foo (Nat.add n 0) = 2`
  guard_target =ₛ foo n = 2
  sorry

example (n : Nat) : foo (n + 1) = 2 := by
  simp only [foo]      -- should not produce `⊢ foo (Nat.add n 0) = 2`
  guard_target =ₛ foo n = 2
  sorry
