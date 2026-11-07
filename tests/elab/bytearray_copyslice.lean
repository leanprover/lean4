import Lean.Util.TestExtern

/-!
Checks that the native implementation of `ByteArray.copySlice` agrees with its reference
implementation on the index-clamping edge cases: `srcOff` at or past the end of `src` (which
returns `dest` unchanged), `len` clamped to the end of `src`, and `destOff` at or past the end
of `dest` (which appends). The in-bounds cases are covered in `2966.lean`.
-/

deriving instance DecidableEq for ByteArray

-- srcOff = src.size: dest returned unchanged
test_extern ByteArray.copySlice ⟨#[1,2,3]⟩ 3 ⟨#[4,5,6,7]⟩ 1 2
-- srcOff past the end of src: dest returned unchanged (early-return path)
test_extern ByteArray.copySlice ⟨#[1,2,3]⟩ 5 ⟨#[4,5,6,7]⟩ 1 2
test_extern ByteArray.copySlice ⟨#[1,2,3]⟩ 5 ⟨#[4,5,6,7]⟩ 10 20
-- len clamped to the end of src
test_extern ByteArray.copySlice ⟨#[1,2,3]⟩ 1 ⟨#[4,5,6,7]⟩ 0 20
test_extern ByteArray.copySlice ⟨#[1,2,3]⟩ 2 ⟨#[4,5,6,7]⟩ 3 20
-- destOff = dest.size: append
test_extern ByteArray.copySlice ⟨#[1,2,3]⟩ 0 ⟨#[4,5,6,7]⟩ 4 2
-- destOff past the end of dest: clamped to an append
test_extern ByteArray.copySlice ⟨#[1,2,3]⟩ 0 ⟨#[4,5,6,7]⟩ 9 2
-- destOff past the end with len clamped
test_extern ByteArray.copySlice ⟨#[1,2,3]⟩ 1 ⟨#[4,5,6,7]⟩ 9 20
-- len = 0
test_extern ByteArray.copySlice ⟨#[1,2,3]⟩ 1 ⟨#[4,5,6,7]⟩ 2 0
test_extern ByteArray.copySlice ⟨#[1,2,3]⟩ 1 ⟨#[4,5,6,7]⟩ 9 0
-- empty src
test_extern ByteArray.copySlice ⟨#[]⟩ 0 ⟨#[4,5,6,7]⟩ 1 3
test_extern ByteArray.copySlice ⟨#[]⟩ 2 ⟨#[4,5,6,7]⟩ 1 3
-- empty dest
test_extern ByteArray.copySlice ⟨#[1,2,3]⟩ 1 ⟨#[]⟩ 0 2
test_extern ByteArray.copySlice ⟨#[1,2,3]⟩ 1 ⟨#[]⟩ 5 2
-- both empty
test_extern ByteArray.copySlice ⟨#[]⟩ 0 ⟨#[]⟩ 0 0
-- exact := false
test_extern ByteArray.copySlice ⟨#[1,2,3]⟩ 0 ⟨#[4,5,6,7]⟩ 4 2 false
test_extern ByteArray.copySlice ⟨#[1,2,3]⟩ 5 ⟨#[4,5,6,7]⟩ 1 2 false
test_extern ByteArray.copySlice ⟨#[1,2,3]⟩ 1 ⟨#[4,5,6,7]⟩ 9 20 false
