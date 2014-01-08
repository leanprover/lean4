variable T : Type
variable R : Type
variable f : T -> R
coercion f
print environment 2
variable g : T -> R
coercion g
variable h : forall (x : Type), x
coercion h
definition T2 : Type := T
definition R2 : Type := R
variable f2 : T2 -> R2
coercion f2
variable id : T -> T
coercion id
