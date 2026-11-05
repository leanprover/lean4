module

/-! Kernel resource errors must survive `decide +kernel`'s diagnostic fallback (#16262). -/

@[irreducible] def appendList : Nat → List Nat
  | 0 => []
  | n + 1 => appendList n ++ [n]

/-- error: (kernel) deep recursion detected, use `set_option maxRecDepth <num>` to increase the limit -/
#guard_msgs in
set_option maxRecDepth 16 in
example : (appendList 300).length = 300 := by decide +kernel

example : (appendList 300).length = 300 := by decide +kernel

@[irreducible] def total : Nat := (List.range 10000).foldl (· + ·) 0

/-- error: (kernel) deterministic timeout -/
#guard_msgs in
set_option maxHeartbeats 100 in
example : total = 49995000 := by decide +kernel

example : total = 49995000 := by decide +kernel
