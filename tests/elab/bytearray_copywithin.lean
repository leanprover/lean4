import Lean.Util.TestExtern

/-!
Checks that the native implementation of `ByteArray.copyWithin` agrees with its reference
implementation (`copySlice` with the same array as source and destination), across overlapping
ranges in both directions, growth past the old size, and the index-clamping edge cases.
-/

deriving instance DecidableEq for ByteArray

-- interior copy, non-overlapping ranges
test_extern ByteArray.copyWithin ⟨#[0,1,2,3,4,5,6,7,8,9]⟩ 0 6 3
-- overlapping ranges, source before destination
test_extern ByteArray.copyWithin ⟨#[0,1,2,3,4,5,6,7,8,9]⟩ 2 4 5
-- overlapping ranges, destination before source
test_extern ByteArray.copyWithin ⟨#[0,1,2,3,4,5,6,7,8,9]⟩ 4 2 5
-- srcOff = destOff
test_extern ByteArray.copyWithin ⟨#[0,1,2,3,4,5,6,7,8,9]⟩ 3 3 4
-- append at the end
test_extern ByteArray.copyWithin ⟨#[0,1,2,3,4,5,6,7,8,9]⟩ 2 10 5
-- overlapping ranges that grow the array
test_extern ByteArray.copyWithin ⟨#[0,1,2,3,4,5,6,7,8,9]⟩ 3 8 6
-- destOff beyond the end is clamped to the end
test_extern ByteArray.copyWithin ⟨#[0,1,2,3,4,5,6,7,8,9]⟩ 2 15 5
-- len clamped to the end of the source
test_extern ByteArray.copyWithin ⟨#[0,1,2,3,4,5,6,7,8,9]⟩ 7 0 20
test_extern ByteArray.copyWithin ⟨#[0,1,2,3,4,5,6,7,8,9]⟩ 7 9 20
-- append at the end with len clamped
test_extern ByteArray.copyWithin ⟨#[0,1,2,3,4,5,6,7,8,9]⟩ 7 10 20
-- srcOff = size
test_extern ByteArray.copyWithin ⟨#[0,1,2,3,4,5,6,7,8,9]⟩ 10 0 3
-- srcOff = size with destOff beyond the end
test_extern ByteArray.copyWithin ⟨#[0,1,2,3,4,5,6,7,8,9]⟩ 10 15 3
-- srcOff beyond the end: no change
test_extern ByteArray.copyWithin ⟨#[0,1,2,3,4,5,6,7,8,9]⟩ 12 0 3
-- len = 0
test_extern ByteArray.copyWithin ⟨#[0,1,2,3,4,5,6,7,8,9]⟩ 3 5 0
-- len = 0 with destOff beyond the end
test_extern ByteArray.copyWithin ⟨#[0,1,2,3,4,5,6,7,8,9]⟩ 3 15 0
-- empty array
test_extern ByteArray.copyWithin ⟨#[]⟩ 0 0 0
test_extern ByteArray.copyWithin ⟨#[]⟩ 1 2 3
-- exact := false
test_extern ByteArray.copyWithin ⟨#[0,1,2,3,4,5,6,7,8,9]⟩ 2 10 5 false
test_extern ByteArray.copyWithin ⟨#[0,1,2,3,4,5,6,7,8,9]⟩ 4 2 5 false
