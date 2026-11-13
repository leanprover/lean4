/-! Rewrites its own source file during elaboration if `LAKE_TEST_TOUCH` is set. -/

#eval show IO Unit from do
  if (← IO.getEnv "LAKE_TEST_TOUCH").isSome then
    IO.FS.writeFile "Foo.lean" (← IO.FS.readFile "Foo.lean")
