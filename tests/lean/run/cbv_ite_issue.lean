set_option cbv.warning false

/--
error: unsolved goals
⊢ (if true = false then 5 else 7) = 7
-/
#guard_msgs in
example : (if (true = false) then 5 else 7) = 7 := by
  conv =>
    lhs
    cbv

example : (if (true = ((fun x => x) true)) then 5 else 7) = 5 := by
  conv =>
    lhs
    cbv

/--
error: unsolved goals
⊢ (if { byteIdx := 1 } = { byteIdx := 2 } then 5 else 42) = 42
-/
#guard_msgs in
example : (if (String.Pos.Raw.mk 1 = String.Pos.Raw.mk 2) then 5 else 42) = 42 := by
  conv =>
    lhs
    cbv

example : (if (String.Pos.Raw.mk 1 = String.Pos.Raw.mk 1) then 5 else 42) = 5 := by
  conv =>
    lhs
    cbv

/--
error: unsolved goals
⊢ (if x : { byteIdx := 1 } = { byteIdx := 2 } then 5 else 42) = 42
-/
#guard_msgs in
example : (if _ : String.Pos.Raw.mk 1 = String.Pos.Raw.mk 2 then 5 else 42) = 42 := by
  conv =>
    lhs
    cbv

example : (if _ : String.Pos.Raw.mk 1 = String.Pos.Raw.mk 1 then 5 else 42) = 5 := by
  conv =>
    lhs
    cbv
