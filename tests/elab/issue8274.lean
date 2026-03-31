set_option linter.unusedVariables false

noncomputable def myTest (x : List Bool) : Bool :=
  match hx : x with
  | x'@hx':(x::xs) => false
  | x'@([]) => true

-- #check myTest.match_1
/--
info: private def myTest.match_1.splitter.{u_1} : (motive : List Bool → Sort u_1) →
  (x : List Bool) →
    ((x_1 : Bool) → (xs : List Bool) → x = x_1 :: xs → motive (x_1 :: xs)) → (x = [] → motive []) → motive x :=
fun motive x h_1 h_2 =>
  (fun x_1 => List.casesOn (motive := fun x_2 => x = x_2 → motive x_2) x_1 h_2 fun head tail => h_1 head tail) x ⋯
-/
#guard_msgs in
#print myTest.match_1.splitter

#guard_msgs in
example : myTest [] := by unfold myTest; split; contradiction; rfl
