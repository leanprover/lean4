import Lean.Util.TestExtern

instance : BEq ByteArray where
  beq x y := x.data == y.data

test_extern Nat.add 12 37
test_extern 4 + 5

test_extern ByteArray.copySlice ⟨#[1,2,3]⟩ 1 ⟨#[4, 5, 6, 7, 8, 9, 10, 11, 12, 13]⟩ 0 6
