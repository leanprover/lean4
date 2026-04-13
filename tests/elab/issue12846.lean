set_option backward.do.legacy false

def test : IO Bool := do
  let a ← pure 25
