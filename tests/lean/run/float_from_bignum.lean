def check (b : Bool) : IO Unit :=
  unless b do
    throw $ IO.userError "check failed"

def tst1 : IO Unit := do
  check (Nat.toFloat (10^40) > Nat.toFloat (10^30));
  check (Nat.toFloat (10^40) >= Nat.toFloat (10^30));
  check (Nat.toFloat (10^40) == Nat.toFloat (10^40));
  check (Nat.toFloat (10^80) > Nat.toFloat (10^40));
  pure ()

#eval tst1
