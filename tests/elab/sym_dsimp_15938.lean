def mycomp (f g : Nat → Nat) (x : Nat) : Nat := f (g x)
theorem mycomp_eq (f g : Nat → Nat) (x : Nat) : mycomp f g x = f (g x) := rfl

variable (op : Nat → Nat → Nat → Nat → Nat) (f g : Nat → Nat) (t0 : Nat)

abbrev Goal15 : Prop :=
  let t1 := op t0 t0 t0 t0
  let t2 := op t1 t1 t1 t1
  let t3 := op t2 t2 t2 t2
  let t4 := op t3 t3 t3 t3
  let t5 := op t4 t4 t4 t4
  let t6 := op t5 t5 t5 t5
  let t7 := op t6 t6 t6 t6
  let t8 := op t7 t7 t7 t7
  let t9 := op t8 t8 t8 t8
  let t10 := op t9 t9 t9 t9
  let t11 := op t10 t10 t10 t10
  let t12 := op t11 t11 t11 t11
  let t13 := op t12 t12 t12 t12
  let t14 := op t13 t13 t13 t13
  let t15 := op t14 t14 t14 t14
  mycomp f g t15 = f (g t15)

example : Goal15 op f g t0 := by
  sym =>
    intros
    dsimp [*, mycomp_eq]
    finish
