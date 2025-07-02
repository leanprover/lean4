/-!
# Improved `simpa` error messages

Updated error message to show the elaborated term rather than `h✝`
-/

/--
error: type mismatch, term
  hp
after simplification has type
  p
but is expected to have type
  p ∧ q
-/
#guard_msgs in
example (p q : Prop) (hp : p ∧ True) : p ∧ q ∧ True := by
  simpa using hp

/--
error: type mismatch, term
  fun x => x
after simplification has type
  True
but is expected to have type
  False
-/
#guard_msgs in
example : False := by
  simpa using (fun x : True => x)
