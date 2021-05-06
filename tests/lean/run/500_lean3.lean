example (foo bar : OptionM Nat) : False := by
  have do { let x ← bar; foo } = bar >>= fun x => foo from rfl
  admit
  done
