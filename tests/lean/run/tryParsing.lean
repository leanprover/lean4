example : IO Unit := do
  try
    for _ in [1] do
      try
        pure ()
      catch _ => unreachable!
  catch _ => unreachable!

example : IO Unit := do
  try
    for _ in [1] do
      try
        pure ()
      catch _ => unreachable!
  finally
    pure ()

example : IO Unit := do
  if true then
    pure ()
  else try
    pure ()
  catch _ =>
    pure ()

example : IO Unit := do
  try
    if true then
      pure ()
    else try
      pure ()
    catch _ =>
      pure ()
  catch _ =>
    pure ()

example : IO Unit := do
  try
    if true then
      pure ()
    else try
        pure ()
      catch _ =>
        pure ()
  catch _ =>
    pure ()

example : IO Unit := do
  try
    let _ ← try
      pure ()
    catch _ =>
      pure ()
  catch _ =>
    pure ()

example : IO Unit := do
  try
    let _ ← try
        pure ()
      catch _ =>
        pure ()
  catch _ =>
    pure ()
