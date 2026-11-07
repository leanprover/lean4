/-!
Regression test for #15938: `Sym.dsimp` called `acLt` on every rewrite, even for
non-permutation theorems, which timed out on large expressions.
-/

def mycomp (f g : Nat → Nat) (x : Nat) : Nat := f (g x)
theorem mycomp_eq (f g : Nat → Nat) (x : Nat) : mycomp f g x = f (g x) := rfl

variable (op : Nat → Nat → Nat → Nat → Nat) (f g : Nat → Nat) (t0 : Nat)

abbrev Goal : Prop :=
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
  mycomp f g t12 = f (g t12)

example : Goal op f g t0 := by
  sym =>
    intros
    dsimp [*, mycomp_eq]
    finish
