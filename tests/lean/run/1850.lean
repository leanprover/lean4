example : Nat :=
  let n := 0
  n.succ + (m |>.succ) + m.succ
where
  m := 1
