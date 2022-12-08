variable (t1 t2 t3 t4 : Nat)
variable (pf12 : t1 = t2) (pf23 : t2 = t3) (pf34 : t3 = t4)

theorem foo : t1 = t4 :=
  calc
    t1 = t2 := pf12
     _ = t3 := pf23
     _ = t4 := pf34

variable (t5 : Nat)
variable (pf23' : t2 < t3) (pf45' : t4 < t5)

instance [LT α] : Trans (α := α) (· < ·) (· < ·) (· < ·) where
  trans := sorry

theorem foo' : t1 < t5 :=
  let p := calc
   t1 = t2 := pf12
    _ < t3 := pf23'
    _ = t4 := pf34
    _ < t5 := pf45'
  -- dedent terminates the block
  p
