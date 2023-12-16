import Lean

def testCopySlice (src : Array UInt8) (srcOff : Nat) (dest : Array UInt8) (destOff len : Nat) : Bool :=
  (ByteArray.copySlice ⟨src⟩ srcOff ⟨dest⟩ destOff len |>.toList) ==
    (ByteArray.copySlice ⟨src⟩ srcOff ⟨dest⟩ destOff len |>.toList)

-- We verify that the `@[extern]` implementation of `ByteArray.copySlice` matches the formal definition,
-- by equating two copies using `==`, unfolding the definition of one, and then calling `native_decide`
macro "testCopySliceTactic" : tactic =>
  `(tactic|
      (dsimp [testCopySlice]
       conv =>
        congr
        congr
        dsimp [ByteArray.copySlice]
       native_decide))

-- These used to fail, as reported in #2966

example : testCopySlice #[1,2,3] 1 #[4, 5, 6, 7, 8, 9, 10, 11, 12, 13] 0 6 := by
  testCopySliceTactic

example : testCopySlice #[1,2,3] 1 #[4, 5, 6, 7, 8, 9, 10, 11, 12, 13] 0 20 := by
  testCopySliceTactic

example : testCopySlice #[1,2,3] 1 #[4, 5, 6] 0 6 := by
  testCopySliceTactic

example : testCopySlice #[1,2,3] 1 #[4, 5, 6, 7, 8, 9, 10, 11, 12, 13] 1 6 := by
  testCopySliceTactic

example : testCopySlice #[1,2,3] 1 #[4, 5, 6, 7, 8, 9, 10, 11, 12, 13] 1 20 := by
  testCopySliceTactic

example : testCopySlice #[1,2,3] 0 #[4, 5, 6, 7, 8, 9, 10, 11, 12, 13] 0 6 := by
  testCopySliceTactic

example : testCopySlice #[1,2,3] 0 #[4, 5, 6, 7, 8, 9, 10, 11, 12, 13] 0 20 := by
  testCopySliceTactic

example : testCopySlice #[1,2,3] 0 #[4, 5, 6, 7, 8, 9, 10, 11, 12, 13] 1 6 := by
  testCopySliceTactic

example : testCopySlice #[1,2,3] 0 #[4, 5, 6, 7, 8, 9, 10, 11, 12, 13] 1 20 := by
  testCopySliceTactic


-- These worked prior to #2966; extra text cases can't hurt!

example : testCopySlice #[1,2,3] 1 #[4, 5, 6, 7, 8, 9, 10, 11, 12, 13] 0 2 := by
  testCopySliceTactic

example : testCopySlice #[1,2,3] 1 #[4, 5, 6] 0 2 := by
  testCopySliceTactic

example : testCopySlice #[1,2,3] 1 #[4, 5, 6, 7, 8, 9, 10, 11, 12, 13] 1 2 := by
  testCopySliceTactic

example : testCopySlice #[1,2,3] 1 #[4, 5, 6] 1 2 := by
  testCopySliceTactic

example : testCopySlice #[1,2,3] 1 #[4, 5, 6] 1 6 := by
  testCopySliceTactic

example : testCopySlice #[1,2,3] 1 #[4, 5, 6, 7, 8, 9, 10, 11, 12, 13] 0 2 := by
  testCopySliceTactic

example : testCopySlice #[1,2,3] 0 #[4, 5, 6] 0 2 := by
  testCopySliceTactic

example : testCopySlice #[1,2,3] 0 #[4, 5, 6, 7, 8, 9, 10, 11, 12, 13] 1 2 := by
  testCopySliceTactic

example : testCopySlice #[1,2,3] 0 #[4, 5, 6] 1 2 := by
  testCopySliceTactic

example : testCopySlice #[1,2,3] 0 #[4, 5, 6] 1 6 := by
  testCopySliceTactic

example : testCopySlice #[1,2,3] 0 #[4, 5, 6] 0 6 := by
  testCopySliceTactic
