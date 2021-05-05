example : True := by
  apply True.intro
      --^ textDocument/hover

example : True := by
  simp [True.intro]
      --^ textDocument/hover

example (n : Nat) : True := by
  match n with
  | Nat.zero => _
  --^ textDocument/hover
  | n + 1 => _
