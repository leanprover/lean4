set_option pp.raw true

example (n : Nat) : 0 = 0 := by
  match n with
  | _ => simp (config := {decide := false}) -- this is the default, so masks the problem?

example : True := by
  have : True := ⟨⟩
  simp (config := {decide := false}) -- unsolved goals

example : True := by
  let _x : True := ⟨⟩
  simp (config := {decide := false}) -- unsolved goals

example : True := by
  suffices True by simp (config := {decide := false}) -- unsolved goals
  constructor

example : True := by
  show True
  simp (config := {decide := false}) -- unsolved goals
