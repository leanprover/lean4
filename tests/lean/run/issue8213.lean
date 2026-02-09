-- set_option trace.Meta.FunInd true

def myTest {α}
  (mmotive : (x : List α) → Sort v)
  (x : List α)
  (h_1 : (a : α) → (dc : List α) → x = a :: dc → mmotive (a :: dc))
  (h_2 : (x' : List α) → x = x' → mmotive x') : mmotive x :=
  match (generalizing := false) h : x with
  | a :: dc => h_1 a dc h
  | x' => h_2 x' h


/--
error: Failed to realize constant myTest.fun_cases:
  Cannot derive functional cases principle (please report this issue)
    failed to transform matcher, type error when constructing new pre-splitter motive:
      myTest.match_1 (fun x => motive x h_1 h_2) x
    failed with
      Application type mismatch: The argument
        h_1
      has type
        (a : α) → (dc : List α) → x = a :: dc → mmotive (a :: dc)
      but is expected to have type
        (a : α) → (dc : List α) → x✝ = a :: dc → mmotive (a :: dc)
      in the application
        motive x✝ h_1
---
error: Unknown identifier `myTest.fun_cases`
-/
#guard_msgs in
def foo := @myTest.fun_cases
