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
  ⏎
    application type mismatch
      motive mmotive x✝ h_1
    argument
      h_1
    has type
      (a : α) → (dc : List α) → x = a :: dc → mmotive (a :: dc) : Sort (imax (u_1 + 1) (u_1 + 1) v)
    but is expected to have type
      (a : α) → (dc : List α) → x✝ = a :: dc → mmotive (a :: dc) : Sort (imax (u_1 + 1) (u_1 + 1) v)
---
error: unknown identifier 'myTest.fun_cases'
---
error: failed to transform matcher, type error when constructing new pre-splitter motive:
  myTest.match_1 (fun x => motive mmotive x h_1 h_2) x
-/
#guard_msgs in
def foo := @myTest.fun_cases

theorem myTest.match_1.heq_1 {α : Type u}
  (motive : (x : List α) → Sort v)
  (x : List α)
  (h_1 : (a : α) → (dc : List α) → x = a :: dc → motive (a :: dc))
  (h_2 : (x' : List α) → x = x' → motive x')
  (a : α) (dc : List α) (h : x = a :: dc)
  : HEq (myTest.match_1 motive x h_1 h_2) (h_1 a dc h) := by
  subst x
  apply heq_of_eq
  apply myTest.match_1.eq_1 motive a dc h_1 h_2

theorem myTest.match_1.heq_2 {α : Type u}
  (motive : (x : List α) → Sort v)
  (x : List α)
  (h_1 : (a : α) → (dc : List α) → x = a :: dc → motive (a :: dc))
  (h_2 : (x' : List α) → x = x' → motive x')
  (x' : List α)
  (hoverlap : ∀ (a : α) (dc : List α), x' = a :: dc → False)
  (h : x = x')
  : HEq (myTest.match_1 motive x h_1 h_2) (h_2 x' h) := by
  subst x
  apply heq_of_eq
  apply myTest.match_1.eq_2 motive x' h_1 h_2 hoverlap
