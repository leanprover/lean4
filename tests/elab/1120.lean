example : Id Nat := do
  let x ← if true then
    pure 1
  else
    pure 2
  pure x
