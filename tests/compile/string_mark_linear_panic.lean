/-!
Tests that with `LEAN_ABORT_ON_NONLINEAR` set, extending a string marked by `markLinear` while it is
shared aborts instead of silently copying the string. The string is grown past its initial capacity
first, so this also covers that the marker survives reallocation.
-/

def bad (n : Nat) : Nat := Id.run do
  let mut s := "".markLinear
  for _ in 0...n do
    s := s.push 'a'
  let t := s.push 'b'
  return t.length + s.length

def main : IO Unit :=
  IO.println (bad 5)
