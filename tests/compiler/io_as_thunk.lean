def p (s: String) : BaseIO String := do
  match ← (IO.println s).toBaseIO with
  | .ok _ => pure s
  | .error e => pure e.toString


def main : IO PUnit := do
  let _ ← p "aaa"
  let t1 ← (p "bbb").asThunk
  let t2 ← (p "ccc").asThunk
  let _t3 ← (p "ddd").asThunk
  IO.print t2.get
  -- IO.print t1.get
  -- IO.print t2.get
