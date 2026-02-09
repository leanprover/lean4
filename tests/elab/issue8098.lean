example : Id Unit := do
  if let true ← true then pure ()
  if let true <- true then pure ()
  pure ()
