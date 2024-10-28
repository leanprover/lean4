/-!
`simp [invalid]` makes progress which is great for interactive UX, but confusing
when inside a tactic combinator. This checks that without the `recover` flag,
`simp [invalid]` fails.
-/

/-- error: unknown identifier 'does_not_exist' -/
#guard_msgs in
example : 0 + n = n := by
  simp only [does_not_exist, Nat.zero_add]
  done

/--
error: unsolved goals
n : Nat
⊢ 0 + n = n
-/
#guard_msgs in
example : 0 + n = n := by
  first | simp only [does_not_exist, Nat.zero_add] | skip
  done

/-- error: unknown identifier 'does_not_exist' -/
#guard_msgs in
example : 0 + n = n := by
  skip <;> simp only [does_not_exist, Nat.zero_add]
  done

/-- error: unknown identifier 'does_not_exist' -/
#guard_msgs in
example : 0 + n = n := by
  all_goals simp only [does_not_exist, Nat.zero_add]
  done
