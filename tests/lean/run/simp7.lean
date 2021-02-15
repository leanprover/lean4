def f (x : α) := x

theorem ex1 (a : α) (b : List α) : f (a::b = []) = False :=
  by simp [f]

def length : List α → Nat
  | []    => 0
  | a::as => length as + 1

theorem ex2 (a b c : α) (as : List α) : length (a :: b :: as) > length as := by
  simp [length]
  apply Nat.lt.step
  apply Nat.ltSuccSelf

def fact : Nat → Nat
  | 0 => 1
  | x+1 => (x+1) * fact x

theorem ex3 : fact x > 0 := by
  induction x with
  | zero => rfl
  | succ x ih =>
    simp [fact]
    apply Nat.mulPos
    apply Nat.zeroLtSucc
    apply ih
