def append (as bs : List α) : List α :=
  match as with
  | [] => bs
  | a :: as => a :: append as bs

theorem append_nil (as : List α) : append as [] = as := by
  induction as <;> simp_all!

theorem append_nil' (as : List α) : append as [] = as := by
  induction as <;> simp! [*]

theorem append_assoc (as bs cs : List α) : append (append as bs) cs = append as (append bs cs) := by
  induction as <;> simp_all!

theorem append_assoc' (as bs cs : List α) : append (append as bs) cs = append as (append bs cs) := by
  induction as <;> simp! [*]

def g : Nat → Nat
  | 0   => 1
  | n+1 => n + 2

example (a : Nat) : g a > 0 := by
  cases a <;> simp! +arith

example (a : Nat) : g a > 0 := by
  cases a <;> simp! +arith

example (a : Nat) : g a > 0 := by
  cases a <;> simp! +arith +decide [-g]
  simp! +arith

example (a : Nat) (h : b + 2 = 2) : g a > b := by
  cases a <;> simp_all! +arith

example (a : Nat) (h : b + 2 = 2) : g a > b := by
  cases a <;> simp_all! +arith +decide [-g]
  simp! +arith +decide
