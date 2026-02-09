def u (x : Nat) : Nat := do
  let y := x + x
  y * (if y > 100 then 1 else (5 : Nat))
