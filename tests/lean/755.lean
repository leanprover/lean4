def Additive (α : Type) := α

instance [OfNat α 1] : OfNat (Additive α) (nat_lit 0) := ⟨(1 : α)⟩

example : (0 : Nat) = (0 : Additive Nat) := rfl -- Error

def toA (a : Nat) : Additive Nat := a

def Foo (α : Type) := α

instance [OfNat α n] : OfNat (Foo α) n :=
  inferInstanceAs (OfNat α n)

instance [HAdd α α α] : HMul (Foo α) (Foo α) (Foo α) where
  hMul a b := let a : α := a; let b : α := b; let x : α := a + b; x

instance [HAdd α α α] : HSub (Foo α) (Foo α) (Foo α) where
  hSub a b := let a : α := a; let b : α := b; let x : α := a + b; x

instance [HAdd α α α] : HAdd (Foo α) (Foo α) (Foo α) where
  hAdd a b := let a : α := a; let b : α := b; let x : α := a + b + a; x

example : (2 : Nat) * (3 : Nat) = (2 : Foo Nat) * (3 : Foo Nat) :=
  rfl -- Error

example : (2 : Nat) + (3 : Nat) = (2 : Foo Nat) + (3 : Foo Nat) :=
  rfl -- Error

example : (2 : Nat) - (3 : Nat) = (2 : Foo Nat) - (3 : Foo Nat) :=
  rfl -- Error

example : (2 : Nat) + (3 : Nat) = (2 : Foo Nat) * (3 : Foo Nat) :=
  rfl

example : (2 : Nat) + (3 : Nat) + (2 : Nat) = (2 : Foo Nat) + (3 : Foo Nat) :=
  rfl

example : (2 : Nat) + (3 : Nat) = (2 : Foo Nat) - (3 : Foo Nat) :=
  rfl
