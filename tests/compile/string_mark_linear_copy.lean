/-!
Tests that without `LEAN_ABORT_ON_NONLINEAR` set, extending a string marked by `markLinear` while it
is shared silently copies the string instead of aborting.
-/

def bad (n : Nat) : Nat × String × String :=
  let s := (String.ofList (List.replicate n 'a')).markLinear
  let t := s.push 'b'
  (t.length + s.length, s, t)

def main : IO Unit := do
  let (n, s, t) := bad 3
  IO.println n
  IO.println s
  IO.println t
