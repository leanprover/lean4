def test1 (a : Nat) : Nat :=
  let f a :=
    dbg_trace s!"{a}"
    a
  let g a :=
    dbg_trace s!"{a + 0}"
    a
  (f a) + (g a)

def main : IO Unit :=
  -- Use `eprintln` because that is what `dbg_trace` uses.
  IO.eprintln f!"{test1 1}"

