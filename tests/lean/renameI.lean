example : (m n : Nat) → m = n := by
  intro y y
  rename_i x
  trace_state
  admit

example : (m n : Nat) → m = n := by
  intro a.b a.b
  rename_i x
  trace_state
  admit

example : (m o p n: Nat) → m + p = n + o := by
  intro a.b _ _ a.b
  rename_i x _ y
  trace_state
  admit
