/-!
Tests that a definition whose body eliminates an empty type has an empty list of equation lemmas,
and that `simp` can still unfold it.
-/

def f (x : Empty) : Nat := nomatch x

def h : Fin 0 → Nat := fun i => nomatch i

def g : Empty → Nat → Nat
  | x, _ => nomatch x

/-- info: equations: -/
#guard_msgs in
#print equations f

/-- info: equations: -/
#guard_msgs in
#print equations h

/-- info: equations: -/
#guard_msgs in
#print equations g

example (x : Empty) : f x = 0 := by
  simp only [f]
  exact nomatch x
