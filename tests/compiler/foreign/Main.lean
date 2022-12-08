import Main.S

def main : IO Unit := do
  IO.println (mkS 10 20 "hello").addXY
  IO.println (mkS 10 20 "hello").string
  appendToGlobalS "foo"
  appendToGlobalS "bla"
  getGlobalString >>= IO.println
  updateGlobalS (mkS 0 0 "world")
  getGlobalString >>= IO.println
  pure ()
