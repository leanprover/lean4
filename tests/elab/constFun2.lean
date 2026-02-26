structure ConstantFunction (α β : Type) where
  f : α → β
  h : ∀ a b, f a = f b

instance : CoeFun (ConstantFunction α β) (fun _ => α → β) where
  coe s := s.f

instance : Coe (ConstantFunction α β) (α → β) where
  coe s := s.f

def zeroNatNat : ConstantFunction Nat Nat where
  f x    := 0
  h a b  := rfl

def tst1 (x : Nat) : Nat :=
  zeroNatNat x

def tst2 (xs : List Nat) : List Nat :=
  [1, 2].map zeroNatNat
