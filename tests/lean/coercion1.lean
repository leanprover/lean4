Variable T : Type
Variable R : Type
Variable f : T -> R
Coercion f
print Environment 2
Variable g : T -> R
Coercion g
Variable h : Pi (x : Type), x
Coercion h
Definition T2 : Type := T
Definition R2 : Type := R
Variable f2 : T2 -> R2
Coercion f2
Variable id : T -> T
Coercion id
