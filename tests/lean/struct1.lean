--

structure A (α : Type) where
(x : α)

structure B (α : Type) where
(x : α)

structure S : Nat where -- error expected Type
(x : Nat)

structure S extends Nat → Nat where -- error expected structure
(x : Nat)
set_option structureDiamondWarning true in
structure S' extends A Nat, B Nat where -- error field `x` already declared
(x : Nat)
structure SDup extends A Nat, A Nat where -- duplicate parent structure 'A'

structure S extends A Nat, B Bool where -- error field `x` from `B` has already been declared
(x : Nat)

structure S1 where
(_x : Nat)

structure S2 where
(x _y : Nat)

structure S where
(x : Nat)
(x : Nat) -- error

structure S extends A Nat where
(x : Nat) -- error

structure S' extends A Nat where
(x := true) -- error type mismatch

structure S extends A Nat where
(x : Bool := true) -- error omit type

structure S'' where
(x : Nat := true) -- error type mismatch

private structure S where
private mk :: (x : Nat)

private structure S where
protected mk :: (x : Nat)

private structure S where
protected (x : Nat)

private structure S where
mk2 :: (x : Nat)

#check S
#check S.mk2
