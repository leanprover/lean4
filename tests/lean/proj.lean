import logic

inductive vector (T : Type) : nat → Type :=
| nil {} : vector T nat.zero
| cons : T → ∀{n}, vector T n → vector T (nat.succ n)

#projections or
#projections and
#projections eq.refl
#projections eq
#projections vector

inductive point :=
mk : nat → nat → point

#projections point :: x y z

#projections point :: x y

#projections point :: x y

inductive funny : nat → Type :=
mk : Π (a : nat), funny a

#projections funny
