structure ConstantFunction where
  domain : Type
  range  : Type
  f      : domain → range
  h      : ∀ a b, f a = f b

instance : CoeFun ConstantFunction (fun s => s.domain → s.range) where
  coe s := s.f

def zeroNatNat : ConstantFunction where
  domain := Nat
  range  := Nat
  f x    := 0
  h a b  := rfl

def tst (x : Nat) : Nat :=
  zeroNatNat x
