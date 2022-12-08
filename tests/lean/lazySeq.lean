partial def loop (x : Nat) : Nat :=
  dbg_trace x
  loop (x+1) + 1

def act1 : IO Unit :=
  throw (IO.userError "act1 failed")

def act2 : IO Unit :=
  act1 *> IO.println (loop 0) -- `loop 0` should not be executed

def act3 : IO Unit :=
  try act2 catch ex => IO.println s!"error: {ex}"

#eval act3
