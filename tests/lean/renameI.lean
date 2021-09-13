example : (m n : Nat) → m = n := by
  intro y y
  renameI x
  traceState
  admit

example : (m n : Nat) → m = n := by
  intro a.b a.b
  renameI x
  traceState
  admit

example : (m o p n: Nat) → m + p = n + o := by
  intro a.b _ _ a.b
  renameI x _ y
  traceState
  admit
