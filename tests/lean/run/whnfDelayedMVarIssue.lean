def Nat.isZero (n : Nat) :=
  n == 0

def test (preDefs : Array (Array Nat)) : IO Unit := do
  for preDefs in preDefs do
    let preDef := preDefs[0]
    if preDef.isZero then
      pure ()
    else
      IO.println "error"
