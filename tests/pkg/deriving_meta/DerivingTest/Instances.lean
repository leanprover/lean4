module
public import DerivingTest.Handlers

instance : ToData Nat where
  convert := .nat

instance : ToData Int where
  convert := .int

instance : ToData String where
  convert := .string

instance : ToData UInt8 where
  convert x := .nat x.toNat

instance : ToData UInt16 where
  convert x := .nat x.toNat

instance : ToData UInt32 where
  convert x := .nat x.toNat

instance : ToData UInt64 where
  convert x := .nat x.toNat

instance : ToData USize where
  convert x := .nat x.toNat

instance [ToData α] : ToData (Array α) where
  convert x := .array <| x.map ToData.convert
