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

#guard ByteArray.ugetUInt16BE ⟨#[1, 2, 3, 4]⟩ 1 == 0x0203
#guard ByteArray.ugetUInt16LE ⟨#[1, 2, 3, 4]⟩ 1 == 0x0302
#guard ByteArray.ugetUInt32BE ⟨#[1, 2, 3, 4]⟩ 0 == 0x01020304
#guard ByteArray.ugetUInt32LE ⟨#[1, 2, 3, 4]⟩ 0 == 0x04030201
#guard ByteArray.ugetUInt64BE ⟨#[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]⟩ 2 == 0x030405060708090A
#guard ByteArray.ugetUInt64LE ⟨#[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]⟩ 2 == 0x0A09080706050403

#guard ByteArray.usetUInt16BE ⟨#[0, 0, 0, 0, 0, 0, 0, 0]⟩ 3 0x0708 == ⟨#[0, 0, 0, 7, 8, 0, 0, 0]⟩
#guard ByteArray.usetUInt16LE ⟨#[0, 0, 0, 0, 0, 0, 0, 0]⟩ 3 0x0708 == ⟨#[0, 0, 0, 8, 7, 0, 0, 0]⟩
#guard ByteArray.usetUInt32BE ⟨#[0, 0, 0, 0, 0, 0, 0, 0]⟩ 4 0x01050708 == ⟨#[0, 0, 0, 0, 1, 5, 7, 8]⟩
#guard ByteArray.usetUInt32LE ⟨#[0, 0, 0, 0, 0, 0, 0, 0]⟩ 4 0x01050708 == ⟨#[0, 0, 0, 0, 8, 7, 5, 1]⟩
#guard ByteArray.usetUInt64BE ⟨#[0, 0, 0, 0, 0, 0, 0, 0]⟩ 0 0xff0301040a0b0708 == ⟨#[255, 3, 1, 4, 10, 11, 7, 8]⟩
#guard ByteArray.usetUInt64LE ⟨#[0, 0, 0, 0, 0, 0, 0, 0]⟩ 0 0xff0301040a0b0708 == ⟨#[8, 7, 11, 10, 4, 1, 3, 255]⟩
