open nat

definition f : nat → nat → nat
| n 0 := 0
| 0 n := 1
| n m := arbitrary nat

theorem f_zero_right : ∀ a, f a 0 = 0
| 0        := rfl
| (succ a) := rfl

theorem f_zero_succ (a : nat) : f 0 (a+1) = 1 :=
rfl

theorem f_succ_succ (a b : nat) : f (a+1) (b+1) = arbitrary nat :=
rfl
