inductive Bit where
  | zero
  | one

instance inst0 : OfNat Bit 0 where
  ofNat := Bit.zero

instance : OfNat Bit 1 where
  ofNat := Bit.one

example : Bit := 0
example : Bit := 1
