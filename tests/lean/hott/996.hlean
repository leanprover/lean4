import types.pointed
open pointed

variable A : Type*
variable a : A

-- Type* is notation for the type of pointed types (types with a specified point in them)
definition ex (A : Type*) (v : Σ(x : A), x = x) : v = v :=
obtain (x : A) (p : _), from v,
rfl

print ex
