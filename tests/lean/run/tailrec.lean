def find (P : Nat → Bool) (x : Nat) : Option Nat :=
  if P x then
    some x
  else
    find P (x +1)
termination_by tailrecursion

#print equations find


/--
error: failed to synthesize
  Inhabited (Fin n)
Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
def notinhabited (n m : Nat) : Fin n :=
  notinhabited n (m+1)
termination_by tailrecursion
