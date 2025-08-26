macro "#test " t:term : command =>
  `(#guard $t
    example : $t := by decide)

#test ByteArray.sliceEq' ⟨#[1, 2, 3]⟩ 0 ⟨#[4, 9, 5]⟩ 1 0
#test ByteArray.sliceEq' ⟨#[1, 2, 3]⟩ 0 ⟨#[1, 2, 3]⟩ 0 3
#test ByteArray.sliceEq' ⟨#[1, 2, 3]⟩ 0 ⟨#[0, 1, 2, 3]⟩ 1 3
#test !ByteArray.sliceEq' ⟨#[1, 2, 3]⟩ 0 ⟨#[0, 1, 2, 3]⟩ 0 3
#test !ByteArray.sliceEq' ⟨#[1, 2, 3]⟩ 2 ⟨#[0, 1, 2, 3]⟩ 0 1
#test ByteArray.sliceEq' ⟨#[1, 2, 3]⟩ 2 ⟨#[0, 1, 2, 3]⟩ 3 1
#test ByteArray.mk #[1, 2, 3] = ⟨#[1, 2, 3]⟩
#test ByteArray.mk #[1, 2, 4] ≠ ⟨#[1, 2, 3]⟩
#test ByteArray.mk #[] ≠ ⟨#[1, 2, 3]⟩
#test ByteArray.mk #[1, 2, 3] ≠ ⟨#[]⟩
#test ByteArray.mk #[] = ⟨#[]⟩
#test ByteArray.mk #[0, 1, 5, 7] = ⟨#[0, 1, 5, 7]⟩
#test ByteArray.mk #[0, 1, 5, 7] ≠ ⟨#[7, 5, 1, 0]⟩
#test (ByteArray.replicate 10 42).data == #[42, 42, 42, 42, 42, 42, 42, 42, 42, 42]
#test (ByteArray.replicate 0 3).data == #[]
#test (ByteArray.replicate 3 0).data == #[0, 0, 0]
#test ((ByteArray.replicate 10 42).fill' 3 5 0).data == #[42, 42, 42, 0, 0, 0, 0, 0, 42, 42]
#test (ByteArray.setSize ⟨#[1, 2, 3, 4, 5, 6]⟩ 3).data == #[1, 2, 3]
#test (ByteArray.setSize ⟨#[1, 2, 3, 4, 5, 6]⟩ 10).data == #[1, 2, 3, 4, 5, 6, 0, 0, 0, 0]
#guard (ByteArray.setSize ⟨#[1, 2, 3, 4, 5, 6]⟩ 12345).size == 12345

#test ByteArray.getUInt16BE ⟨#[1, 2, 3, 4]⟩ 1 == 0x0203
#test ByteArray.getUInt16LE ⟨#[1, 2, 3, 4]⟩ 1 == 0x0302
#test ByteArray.getUInt32BE ⟨#[1, 2, 3, 4]⟩ 0 == 0x01020304
#test ByteArray.getUInt32LE ⟨#[1, 2, 3, 4]⟩ 0 == 0x04030201
#test ByteArray.getUInt64BE ⟨#[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]⟩ 2 == 0x030405060708090A
#test ByteArray.getUInt64LE ⟨#[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]⟩ 2 == 0x0A09080706050403

#test ByteArray.setUInt16BE ⟨#[0, 0, 0, 0, 0, 0, 0, 0]⟩ 3 0x0708 == ⟨#[0, 0, 0, 7, 8, 0, 0, 0]⟩
#test ByteArray.setUInt16LE ⟨#[0, 0, 0, 0, 0, 0, 0, 0]⟩ 3 0x0708 == ⟨#[0, 0, 0, 8, 7, 0, 0, 0]⟩
#test ByteArray.setUInt32BE ⟨#[0, 0, 0, 0, 0, 0, 0, 0]⟩ 4 0x01050708 == ⟨#[0, 0, 0, 0, 1, 5, 7, 8]⟩
#test ByteArray.setUInt32LE ⟨#[0, 0, 0, 0, 0, 0, 0, 0]⟩ 4 0x01050708 == ⟨#[0, 0, 0, 0, 8, 7, 5, 1]⟩
#test ByteArray.setUInt64BE ⟨#[0, 0, 0, 0, 0, 0, 0, 0]⟩ 0 0xff0301040a0b0708 == ⟨#[255, 3, 1, 4, 10, 11, 7, 8]⟩
#test ByteArray.setUInt64LE ⟨#[0, 0, 0, 0, 0, 0, 0, 0]⟩ 0 0xff0301040a0b0708 == ⟨#[8, 7, 11, 10, 4, 1, 3, 255]⟩
