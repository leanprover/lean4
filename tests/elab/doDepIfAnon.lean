-- Test that anonymous `if _ : cond then ...` works in do blocks (new do elaborator)
set_option backward.do.legacy false
def testDepIfAnon (n : Nat) : IO Unit := do
  if _ : n > 0 then
    IO.println "positive"
  else
    IO.println "zero"

-- Test the named variant too
def testDepIfNamed (n : Nat) : IO Unit := do
  if h : n > 0 then
    IO.println s!"positive: {n} > 0"
  else
    IO.println "zero"
