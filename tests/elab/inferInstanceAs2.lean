/-!
Tests for `inferInstanceAs` against expected types whose explicit arguments wrap a
non-reducible defined type (`Zmod n` here, which unfolds to `Nat ⧸ n`). User-placed
`_` placeholders in the `inferInstanceAs` type argument must be resolved by matching
against the expected type without getting blocked by the `.instances` transparency
cap on synthetic instance metavariables.
-/

class HasQuotient (A : outParam <| Type u) (B : Type v) where
  Quotient (A) : B → Type max u v

notation:35 G " ⧸ " H:34 => HasQuotient.Quotient G H

class Foo (α : Type) [Neg α] where

instance {n : Nat} : Foo (Fin n) where

instance : HasQuotient Nat Nat where
  Quotient n := Fin n

instance {n : Nat} : Neg (Nat ⧸ n) :=
  inferInstanceAs <| Neg (Fin n)

instance {n : Nat} : Foo (Nat ⧸ n) :=
  inferInstanceAs <| Foo (Fin n)

def Zmod (n : Nat) :=
  Nat ⧸ n
deriving Neg

instance {n : Nat} : Foo (Zmod n) :=
  inferInstanceAs <| Foo (_ ⧸ _)

instance {n : Nat} : Foo (Zmod n) :=
  inferInstanceAs <| Foo (Nat ⧸ n)

set_option backward.isDefEq.respectTransparency.instances false in
instance {n : Nat} : Foo (Zmod n) :=
  inferInstanceAs <| Foo (_ ⧸ _)
