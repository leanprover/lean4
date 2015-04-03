open nat

definition f : nat → nat → nat
| f _ 0 := 0
| f 0 _ := 1
| f _ _ := arbitrary nat

theorem f_zero_right : ∀ a, f a 0 = 0
| f_zero_right 0        := rfl
| f_zero_right (succ a) := rfl

theorem f_zero_succ (a : nat) : f 0 (a+1) = 1 :=
rfl

theorem f_succ_succ (a b : nat) : f (a+1) (b+1) = arbitrary nat :=
rfl
