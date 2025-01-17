def main (progName : String) (args : List String) := do
  let mut progName := progName
  -- If we get a windows-style full path, replace it with the expected linux output for simplicity
  if progName.endsWith r"tests\compiler\progName.lean.out" then
    progName := "./progName.lean.out"
  IO.println s!"{progName}: {args}"
