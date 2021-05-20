example (foo bar : OptionM Nat) : False := by
  have : do { let x ← bar; foo } = bar >>= fun x => foo := rfl
  admit
  done
