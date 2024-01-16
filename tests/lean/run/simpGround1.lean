set_option trace.Meta.Tactic.simp.ground true

def f1 (as : List Nat) (n : Nat) :=
  match as with
  | [] => []
  | a :: as => (a + n) :: f1 as n

example (h : xs = [6, 7, 8]) : f1 [1, 2, 3] 5 = xs := by
  fail_if_success simp
  simp (config := { ground := true })
  rw [h]

def add2 (a b : Int) : Int :=
  a + a + b

def f2 (as : List Int) (n : Int) :=
  match as with
  | [] => []
  | a :: as => (add2 a n) :: f2 as n

example (h : xs = [-3, 15, -9, 11]) : f2 [1, 10, -2, 8] (-5) = xs := by
  fail_if_success simp
  simp (config := { ground := true })
  rw [h]

def f3 (as : List UInt32) (n : UInt32) :=
  match as with
  | [] => []
  | a :: as => (a + n) :: f3 as n

example (h : xs = [6, 7, 8]) : f3 [1, 2, 3] 5 = xs := by
  fail_if_success simp
  simp (config := { ground := true })
  rw [h]

def f4 (as : List (Fin 50)) (n : Fin 50) :=
  match as with
  | [] => []
  | a :: as => (a + n) :: f4 as n

example (h : xs = [6, 7, 8]) : f4 [1, 2, 3] 5 = xs := by
  fail_if_success simp
  simp (config := { ground := true })
  rw [h]

#check List.instAppendList

example (h : xs = [4, 3, 2]) : ([1, 2, 3].map (· + 1) |>.reverse) = xs := by
  simp (config := { ground := true })
  rw [h]
  done

def rev (as : List α) : List α :=
  match as with
  | [] => []
  | a::as => rev as ++ [a]

example (h : xs = [4, 3, 2]) : (rev <| [1, 2, 3].map (· + 1)) = xs := by
  simp (config := { ground := true })
  rw [h]
  done
