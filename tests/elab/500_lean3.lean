example (foo bar : Option Nat) : False := by
  have : do { let x ← bar; foo } = bar >>= fun x => foo := rfl
  admit
  done
