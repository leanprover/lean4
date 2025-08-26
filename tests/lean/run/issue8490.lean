inductive Aexp where
  | val : Int → Aexp
  | plus : Aexp → Aexp → Aexp

@[simp]
def asimp_const : Aexp -> Aexp
  | .val x    => .val x
  | .plus x y => .plus x y

@[simp]
def optimal' (a : Aexp) : Prop :=
  optimal' a ∧ True
inductive_fixpoint

/--
info: Try this:
  simp_all only [asimp_const, reduceCtorEq]
-/
#guard_msgs in
example (x y : Aexp) (k : Int) (h : asimp_const (.val k) = x.plus y) : optimal' x := by
  simp_all?
