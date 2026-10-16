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
info: myTest.fun_cases.{v, u_1} {α : Type u_1} (mmotive : List α → Sort v)
  (motive :
    (x : List α) →
      ((a : α) → (dc : List α) → x = a :: dc → mmotive (a :: dc)) → ((x' : List α) → x = x' → mmotive x') → Prop)
  (case1 :
    ∀ (a : α) (dc : List α) (h_1 : (a_1 : α) → (dc_1 : List α) → a :: dc = a_1 :: dc_1 → mmotive (a_1 :: dc_1))
      (h_2 : (x' : List α) → a :: dc = x' → mmotive x'), motive (a :: dc) h_1 h_2)
  (case2 :
    ∀ (x' : List α),
      (∀ (a : α) (dc : List α), x' = a :: dc → False) →
        ∀ (h_1 : (a : α) → (dc : List α) → x' = a :: dc → mmotive (a :: dc))
          (h_2 : (x'_1 : List α) → x' = x'_1 → mmotive x'_1), motive x' h_1 h_2)
  (x : List α) (h_1 : (a : α) → (dc : List α) → x = a :: dc → mmotive (a :: dc))
  (h_2 : (x' : List α) → x = x' → mmotive x') : motive x h_1 h_2
-/
#guard_msgs in
#check myTest.fun_cases
