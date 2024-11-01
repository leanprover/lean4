--

structure A (α : Type) :=
(x : α)

structure B (α : Type) :=
(x : α)

structure S : Nat := -- error expected Type
(x : Nat)

structure S extends Nat → Nat := -- error expected structure
(x : Nat)
set_option structureDiamondWarning true in
structure S' extends A Nat, A Bool := -- error field `x` already declared
(x : Nat)

structure S extends A Nat, B Bool := -- error field `x` from `B` has already been declared
(x : Nat)

structure S1 :=
(_x : Nat)

structure S2 :=
(x _y : Nat)

structure S :=
(x : Nat)
(x : Nat) -- error

structure S extends A Nat :=
(x : Nat) -- error

structure S' extends A Nat :=
(x := true) -- error type mismatch

structure S extends A Nat :=
(x : Bool := true) -- error omit type

structure S'' :=
(x : Nat := true) -- error type mismatch

private structure S :=
private mk :: (x : Nat)

private structure S :=
protected mk :: (x : Nat)

private structure S :=
protected (x : Nat)

private structure S :=
mk2 :: (x : Nat)

#check S
#check S.mk2
