import Init.Data.ByteArray.AdditionalOperations

#guard ByteArray.sliceEq' ⟨#[1, 2, 3]⟩ 0 ⟨#[4, 9, 5]⟩ 1 0
#guard ByteArray.sliceEq' ⟨#[1, 2, 3]⟩ 0 ⟨#[1, 2, 3]⟩ 0 3
#guard ByteArray.sliceEq' ⟨#[1, 2, 3]⟩ 0 ⟨#[0, 1, 2, 3]⟩ 1 3
#guard !ByteArray.sliceEq' ⟨#[1, 2, 3]⟩ 0 ⟨#[0, 1, 2, 3]⟩ 0 3
#guard !ByteArray.sliceEq' ⟨#[1, 2, 3]⟩ 2 ⟨#[0, 1, 2, 3]⟩ 0 1
#guard ByteArray.sliceEq' ⟨#[1, 2, 3]⟩ 2 ⟨#[0, 1, 2, 3]⟩ 3 1
#guard ByteArray.mk #[1, 2, 3] = ⟨#[1, 2, 3]⟩
#guard ByteArray.mk #[1, 2, 4] ≠ ⟨#[1, 2, 3]⟩
#guard ByteArray.mk #[] ≠ ⟨#[1, 2, 3]⟩
#guard ByteArray.mk #[1, 2, 3] ≠ ⟨#[]⟩
#guard ByteArray.mk #[] = ⟨#[]⟩
#guard ByteArray.mk #[0, 1, 5, 7] = ⟨#[0, 1, 5, 7]⟩
#guard ByteArray.mk #[0, 1, 5, 7] ≠ ⟨#[7, 5, 1, 0]⟩
#guard (ByteArray.replicate 10 42).data == #[42, 42, 42, 42, 42, 42, 42, 42, 42, 42]
#guard (ByteArray.replicate 0 3).data == #[]
#guard (ByteArray.replicate 3 0).data == #[0, 0, 0]
#guard ((ByteArray.replicate 10 42).fill' 3 5 0).data == #[42, 42, 42, 0, 0, 0, 0, 0, 42, 42]
#guard (ByteArray.setSize ⟨#[1, 2, 3, 4, 5, 6]⟩ 3).data == #[1, 2, 3]
#guard (ByteArray.setSize ⟨#[1, 2, 3, 4, 5, 6]⟩ 10).data == #[1, 2, 3, 4, 5, 6, 0, 0, 0, 0]
#guard (ByteArray.setSize ⟨#[1, 2, 3, 4, 5, 6]⟩ 12345).size == 12345
