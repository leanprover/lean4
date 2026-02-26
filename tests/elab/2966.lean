import Lean.Util.TestExtern

deriving instance DecidableEq for ByteArray

-- These used to fail, as reported in #2966
test_extern ByteArray.copySlice ⟨#[1,2,3]⟩ 1 ⟨#[4, 5, 6, 7, 8, 9, 10, 11, 12, 13]⟩ 0 6

test_extern ByteArray.copySlice ⟨#[1,2,3]⟩ 1 ⟨#[4, 5, 6, 7, 8, 9, 10, 11, 12, 13]⟩ 0 6
test_extern ByteArray.copySlice ⟨#[1,2,3]⟩ 1 ⟨#[4, 5, 6, 7, 8, 9, 10, 11, 12, 13]⟩ 0 20

test_extern ByteArray.copySlice ⟨#[1,2,3]⟩ 1 ⟨#[4, 5, 6]⟩ 0 6
test_extern ByteArray.copySlice ⟨#[1,2,3]⟩ 1 ⟨#[4, 5, 6, 7, 8, 9, 10, 11, 12, 13]⟩ 1 6
test_extern ByteArray.copySlice ⟨#[1,2,3]⟩ 1 ⟨#[4, 5, 6, 7, 8, 9, 10, 11, 12, 13]⟩ 1 20
test_extern ByteArray.copySlice ⟨#[1,2,3]⟩ 0 ⟨#[4, 5, 6, 7, 8, 9, 10, 11, 12, 13]⟩ 0 6
test_extern ByteArray.copySlice ⟨#[1,2,3]⟩ 0 ⟨#[4, 5, 6, 7, 8, 9, 10, 11, 12, 13]⟩ 0 20
test_extern ByteArray.copySlice ⟨#[1,2,3]⟩ 0 ⟨#[4, 5, 6, 7, 8, 9, 10, 11, 12, 13]⟩ 1 6
test_extern ByteArray.copySlice ⟨#[1,2,3]⟩ 0 ⟨#[4, 5, 6, 7, 8, 9, 10, 11, 12, 13]⟩ 1 20

-- These worked prior to #2966; extra text cases can't hurt!

test_extern ByteArray.copySlice ⟨#[1,2,3]⟩ 1 ⟨#[4, 5, 6, 7, 8, 9, 10, 11, 12, 13]⟩ 0 2
test_extern ByteArray.copySlice ⟨#[1,2,3]⟩ 1 ⟨#[4, 5, 6]⟩ 0 2
test_extern ByteArray.copySlice ⟨#[1,2,3]⟩ 1 ⟨#[4, 5, 6, 7, 8, 9, 10, 11, 12, 13]⟩ 1 2
test_extern ByteArray.copySlice ⟨#[1,2,3]⟩ 1 ⟨#[4, 5, 6]⟩ 1 2
test_extern ByteArray.copySlice ⟨#[1,2,3]⟩ 1 ⟨#[4, 5, 6]⟩ 1 6
test_extern ByteArray.copySlice ⟨#[1,2,3]⟩ 1 ⟨#[4, 5, 6, 7, 8, 9, 10, 11, 12, 13]⟩ 0 2
test_extern ByteArray.copySlice ⟨#[1,2,3]⟩ 0 ⟨#[4, 5, 6]⟩ 0 2
test_extern ByteArray.copySlice ⟨#[1,2,3]⟩ 0 ⟨#[4, 5, 6, 7, 8, 9, 10, 11, 12, 13]⟩ 1 2
test_extern ByteArray.copySlice ⟨#[1,2,3]⟩ 0 ⟨#[4, 5, 6]⟩ 1 2
test_extern ByteArray.copySlice ⟨#[1,2,3]⟩ 0 ⟨#[4, 5, 6]⟩ 1 6
test_extern ByteArray.copySlice ⟨#[1,2,3]⟩ 0 ⟨#[4, 5, 6]⟩ 0 6
