import Std.Data.ByteSlice

-- Test data
def ba := ByteArray.mk #[1,2,3,4,5,6,7,8,9,10]
def bb := ByteArray.mk #[1,2,3,4,5,6,7,8,9,10,1,2,3,4,5,6,7,8,9,10]
def emptyArray := ByteArray.mk #[]
def singleByte := ByteArray.mk #[42]

-- Basic slicing tests (existing)
/--
info: [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
-/
#guard_msgs in
#eval bb[10...20] |>.toByteArray

/--
info: [3, 4]
-/
#guard_msgs in
#eval bb[10...20][2...4] |>.toByteArray

/--
info: 4
-/
#guard_msgs in
#eval bb[10...20][2...4] |>.get! 1

/--
info: true
-/
#guard_msgs in
#eval bb[10...20][2...4] |>.contains 4

-- Size function tests
/--
info: 10
-/
#guard_msgs in
#eval ba.toByteSlice.size

/--
info: 0
-/
#guard_msgs in
#eval emptyArray.toByteSlice.size

/--
info: 1
-/
#guard_msgs in
#eval singleByte.toByteSlice.size

/--
info: 5
-/
#guard_msgs in
#eval ba[2...7].size

-- Element access tests
/--
info: 1
-/
#guard_msgs in
#eval ba[0...5][0]!

/--
info: 5
-/
#guard_msgs in
#eval ba[0...5][4]!

-- getD (get with default) tests
/--
info: 3
-/
#guard_msgs in
#eval ba.toByteSlice.getD 2 99

/--
info: 99
-/
#guard_msgs in
#eval ba.toByteSlice.getD 15 99

/--
info: 255
-/
#guard_msgs in
#eval emptyArray.toByteSlice.getD 0 255

-- get! tests (with bounds checking)
/--
info: 0
-/
#guard_msgs in
#eval ba.toByteSlice.get! 15

/--
info: 0
-/
#guard_msgs in
#eval emptyArray.toByteSlice.get! 0

/--
info: 42
-/
#guard_msgs in
#eval singleByte.toByteSlice.get! 0

-- Contains function tests
/--
info: true
-/
#guard_msgs in
#eval ba.toByteSlice.contains 5

/--
info: false
-/
#guard_msgs in
#eval ba.toByteSlice.contains 15

/--
info: false
-/
#guard_msgs in
#eval emptyArray.toByteSlice.contains 1

/--
info: true
-/
#guard_msgs in
#eval bb[5...15].contains 10

-- Equality tests
/--
info: true
-/
#guard_msgs in
#eval ba[0...5] == ba[0...5]

/--
info: true
-/
#guard_msgs in
#eval ba[0...3].toByteArray == bb[0...3].toByteArray

/--
info: false
-/
#guard_msgs in
#eval ba[0...3] == ba[1...4]

/--
info: true
-/
#guard_msgs in
#eval ByteSlice.empty == emptyArray.toByteSlice

-- Edge case: empty slices
/--
info: 0
-/
#guard_msgs in
#eval ByteSlice.empty.size

/--
info: []
-/
#guard_msgs in
#eval ByteSlice.empty.toByteArray

/--
info: false
-/
#guard_msgs in
#eval ByteSlice.empty.contains 0

-- Edge case: slice bounds clamping
/--
info: [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
-/
#guard_msgs in
#eval ba[0...100].toByteArray

/--
info: []
-/
#guard_msgs in
#eval ba[100...200].toByteArray

/--
info: [6, 7, 8, 9, 10]
-/
#guard_msgs in
#eval ba[5...100].toByteArray

-- Foldr function tests
/--
info: 55
-/
#guard_msgs in
#eval ba.toByteSlice.foldr (fun b acc => b.toNat + acc) 0

/--
info: 0
-/
#guard_msgs in
#eval ByteSlice.empty.foldr (fun b acc => b.toNat + acc) 0

/--
info: 42
-/
#guard_msgs in
#eval singleByte.toByteSlice.foldr (fun b acc => b.toNat + acc) 0

-- Nested slicing with element access

/--
info: 7
-/
#guard_msgs in
#eval bb[0...10][5...8][1]!

/--
info: true
-/
#guard_msgs in
#eval bb[0...10][5...8].contains 6

/--
info: false
-/
#guard_msgs in
#eval bb[0...10][5...8].contains 5

-- Size consistency tests
/--
info: 3
-/
#guard_msgs in
#eval bb[0...10][5...8].size

/--
info: 5
-/
#guard_msgs in
#eval bb[5...15][0...5].size

-- Boundary testing with single elements
/--
info: [10]
-/
#guard_msgs in
#eval ba[9...10].toByteArray

/--
info: 1
-/
#guard_msgs in
#eval ba[9...10].size

/--
info: 10
-/
#guard_msgs in
#eval ba[9...10][0]!

-- Out of bounds slice handling
/--
info: []
-/
#guard_msgs in
#eval ba[15...20].toByteArray

/--
info: 0
-/
#guard_msgs in
#eval ba[15...20].size

/--
info: []
-/
#guard_msgs in
#eval ba.toByteSlice.slice 8 3 |>.toByteArray

/--
info: 0
-/
#guard_msgs in
#eval ba.toByteSlice.slice 8 3 |>.size

/--
info: [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
-/
#guard_msgs in
#eval ba.toByteSlice.slice 0 10 |>.toByteArray

/--
info: true
-/
#guard_msgs in
#eval bb[0...10] == bb[10...20]

/--
info: [1, 2, 3]
-/
#guard_msgs in
#eval bb[10...13].toByteArray

-- Testing with different default values in getD
/--
info: 128
-/
#guard_msgs in
#eval ba[0...3].getD 10 128

/--
info: 2
-/
#guard_msgs in
#eval ba[0...3].getD 1 128

def maxByteArray := ByteArray.mk #[255, 0, 128, 1]

/--
info: true
-/
#guard_msgs in
#eval maxByteArray.toByteSlice.contains 255

/--
info: 384
-/
#guard_msgs in
#eval maxByteArray.toByteSlice.foldr (fun b acc => b.toNat + acc) 0

/--
info: [255, 0]
-/
#guard_msgs in
#eval maxByteArray[0...2].toByteArray
