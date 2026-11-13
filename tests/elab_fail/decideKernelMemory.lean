module

/-! Preserve the kernel memory-limit error instead of diagnosing irreducibility (#16262). -/

@[irreducible] def sum : Nat := (List.range 100000).foldl (· + ·) 0

example : sum = 4999950000 := by decide +kernel
