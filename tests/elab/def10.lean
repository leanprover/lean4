def f : Bool → Bool → Nat
  | true, true => 0
  | _, _       => 3

example : f true true = 0 :=
  rfl

def g : Bool → Bool → Bool → Nat
  | true, _,    true  => 1
  | _,   false, false => 2
  | a,   _,     b     => f a b

theorem ex1 : g true true true = 1 := rfl
theorem ex2 : g true false true = 1 := rfl
theorem ex3 : g true false false = 2 := rfl
theorem ex4 : g false false false = 2 := rfl
theorem ex5 : g false true true = 3 := rfl

theorem f_eq (h : a = true → b = true → False) : f a b = 3 := by
  simp (config := { iota := false }) [f]
  split
  · contradiction
  · rfl

theorem ex6 : g x y z > 0 := by
  simp [g]
  split
  next => decide
  next => decide
  next a b c h₁ h₂ => simp (config := { decide := true }) [f_eq h₁]
