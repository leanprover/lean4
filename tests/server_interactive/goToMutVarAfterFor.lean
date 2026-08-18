/-! Go-to-definition on a `mut` variable referenced after a `for` loop resolves to its `let mut`
declaration. -/
--^ waitForILeans

example : Id Nat := do
  let mut myNat := 1
  for i in [1,2,3] do
    myNat := myNat + i
  return myNat
       --^ textDocument/definition
