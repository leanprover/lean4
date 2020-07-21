structure A (α : Type) :=
(x : α)

structure B (α : Type) :=
(x : α)

new_frontend

structure S : Nat := -- error expected Type
(x : Nat)

structure S extends Nat → Nat := -- error expected structure
(x : Nat)

structure S extends A Nat, A Bool := -- error field toA already declared
(x : Nat)

structure S extends A Nat, B Bool := -- error field `x` from `B` has already been declared
(x : Nat)

structure S := -- error '_' is not allowed
(_x : Nat)

structure S := -- error '_' is not allowed
(x _y : Nat)
