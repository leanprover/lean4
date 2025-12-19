import Std.Data.Iterators

open Std.Iterators

/-- info: true -/
#guard_msgs in
#eval "b" ∈ ("a"...="c")

/-- info: [1, 2, 3, 4] -/
#guard_msgs in
#eval (1...=4).toList

/-- info: [2, 3] -/
#guard_msgs in
#eval (1<...4).toList

/-- info: [1, 2, 3] -/
#guard_msgs in
#eval (1...4).toList

/-- info: [1, 2, 3] -/
#guard_msgs in
#eval (1...<4).toList

/-- info: [0, 1, 2, 3, 4] -/
#guard_msgs in
#eval (*...=4).toList

/-- info: 2 -/
#guard_msgs in
#eval (1<...4).size

/-- info: true -/
#guard_msgs in
#eval (1...<1).isEmpty

/-- info: [3, 5, 7, 9, 11, 13] -/
#guard_msgs in
#eval (2<...<15).iter.stepSize 2 |>.toList

example : (1...5).size = 4 := by
  simp [← Std.Rco.size_toArray, Std.Rco.toArray_eq_if_rco]

/-- info: true -/
#guard_msgs in
#eval 1 ∈ (1...=5)

def g (xs : Array Nat) : Nat := Id.run do
  let mut sum := 0
  for h : i in *...<xs.size do
    sum := sum + xs[i]
  return sum

/-- info: 6 -/
#guard_msgs in
#eval g #[1, 2, 3]

def h (n : Nat) : IO Unit := do
  for i in *...n, j in 2...* do
    IO.println s!"i={i}, j={j}"

example (xs : Vector Nat 16) : Id Unit := do
  let mut x := 0
  for _h : i in *...<(12 : Nat) do
    x := x + xs[i]

example (xs : List Nat) (h : xs.length = 16) : Id Unit := do
  let mut x := 0
  for _h : i in *...<(12 : Nat) do
    x := x + xs[i]

example (xs : Array Nat) : Id Unit := do
  let mut x := 0
  for _h : i in *...<(xs.size - 5 : Nat) do
    x := x + xs[i]

example (xs : Array Nat) : Id Unit := do
  let mut x := 0
  for _h : i in *...=xs.size do
    for _h' : i' in *...<i do
      x := x + xs[i']

example {a : Array Nat} (h : a.size = 28) : Id Unit := do
  let mut x := 0
  for h : i in *...(3 : Nat) do
    x := a[1...4][i]

/--
info: i=0, j=2
i=1, j=3
i=2, j=4
i=3, j=5
i=4, j=6
-/
#guard_msgs in
#eval h 5

section Int

example : ((-2)...3).toList = [-2, -1, 0, 1, 2] := by native_decide
example : ((-2)...=3).toList = [-2, -1, 0, 1, 2, 3] := by native_decide

end Int

section UInt

example : ((1 : UInt8)...3).toList = [1, 2] := by native_decide
example : ((-1 : UInt8)...3).toList = [] := by native_decide -- 255 ≤ x < 3 is impossible
example : ((1 : UInt8)...=3).toList = [1, 2, 3] := by native_decide
example : ((250 : UInt8)...-1).toList = [250, 251, 252, 253, 254] := by native_decide
example : (*...(2 : UInt8)).toList = [0, 1] := by native_decide
example : ((255 : UInt8)...*).toList = [255] := by native_decide
example : (*...* : Std.Rii UInt8).toList.length = 256 := by native_decide

example : ((1 : UInt16)...3).toList = [1, 2] := by native_decide
example : ((-1 : UInt16)...3).toList = [] := by native_decide
example : ((1 : UInt16)...=3).toList = [1, 2, 3] := by native_decide
example : ((-4 : UInt16)...-1).toList = [-4, -3, -2] := by native_decide
example : (*...(2 : UInt16)).toList = [0, 1] := by native_decide
example : ((2 ^ 16 - 1 : UInt16)...*).toList = [(2 : UInt16) ^ 16 - 1] := by native_decide
example : (*...* : Std.Rii UInt16).toList.length = 2 ^ 16 := by native_decide

example : ((1 : UInt32)...3).toList = [1, 2] := by native_decide
example : ((-1 : UInt32)...3).toList = [] := by native_decide
example : ((1 : UInt32)...=3).toList = [1, 2, 3] := by native_decide
example : ((-4 : UInt32)...-1).toList = [-4, -3, -2] := by native_decide
example : (*...(2 : UInt32)).toList = [0, 1] := by native_decide
example : ((2 ^ 32 - 1 : UInt32)...*).toList = [(2 : UInt32) ^ 32 - 1] := by native_decide
example : (*...* : Std.Rii UInt32).size = 2 ^ 32 := by native_decide

example : ((1 : UInt64)...3).toList = [1, 2] := by native_decide
example : ((-1 : UInt64)...3).toList = [] := by native_decide
example : ((1 : UInt64)...=3).toList = [1, 2, 3] := by native_decide
example : ((-4 : UInt64)...-1).toList = [-4, -3, -2] := by native_decide
example : (*...(2 : UInt64)).toList = [0, 1] := by native_decide
example : ((2 ^ 64 - 1 : UInt64)...*).toList = [(2 : UInt64) ^ 64 - 1] := by native_decide
example : (*...* : Std.Rii UInt64).size = 2 ^ 64 := by native_decide

example : ((1 : USize)...3).toList = [1, 2] := by native_decide
example : ((-1 : USize)...3).toList = [] := by native_decide
example : ((1 : USize)...=3).toList = [1, 2, 3] := by native_decide
example : ((-4 : USize)...-1).toList = [-4, -3, -2] := by native_decide
example : (*...(2 : USize)).toList = [0, 1] := by native_decide
example : ((2 ^ System.Platform.numBits - 1 : USize)...*).toList =
    [(2 : USize) ^ System.Platform.numBits - 1] := by native_decide
example : (*...* : Std.Rii USize).size = 2 ^ System.Platform.numBits := by native_decide

end UInt

section SInt

example : ((1 : Int8)...3).toList = [1, 2] := by native_decide
example : ((-1 : Int8)...3).toList = [-1, 0, 1, 2] := by native_decide
example : ((1 : Int8)...=3).toList = [1, 2, 3] := by native_decide
example : ((250 : Int8)...-1).toList = [250, 251, 252, 253, 254] := by native_decide
example : ((127 : Int8)...128).toList = [] := by native_decide -- 127 ≤ x < -128 is impossible
example : (*...(-127 : Int8)).toList = [-128] := by native_decide
example : ((127 : Int8)...*).toList = [127] := by native_decide
example : (*...* : Std.Rii Int8).toList.length = 256 := by native_decide

example : ((1 : Int16)...3).toList = [1, 2] := by native_decide
example : ((-1 : Int16)...3).toList = [-1, 0, 1, 2] := by native_decide
example : ((1 : Int16)...=3).toList = [1, 2, 3] := by native_decide
example : ((-4 : Int16)...-1).toList = [-4, -3, -2] := by native_decide
example : ((2 ^ 15 - 1 : Int16)...(2 ^ 15)).toList = [] := by native_decide
example : (*...Int16.minValue + 1).toList = [Int16.minValue] := by native_decide
example : (Int16.maxValue...*).toList = [Int16.maxValue] := by native_decide
example : (*...* : Std.Rii Int16).size = 2 ^ 16 := by native_decide

example : ((1 : Int32)...3).toList = [1, 2] := by native_decide
example : ((-1 : Int32)...3).toList = [-1, 0, 1, 2] := by native_decide
example : ((1 : Int32)...=3).toList = [1, 2, 3] := by native_decide
example : ((-4 : Int32)...-1).toList = [-4, -3, -2] := by native_decide
example : ((2 ^ 31 - 1 : Int32)...(2 ^ 31)).toList = [] := by native_decide
example : (*...Int32.minValue + 1).toList = [Int32.minValue] := by native_decide
example : (Int32.maxValue...*).toList = [Int32.maxValue] := by native_decide
example : (*...* : Std.Rii Int32).size = 2 ^ 32 := by native_decide

example : ((1 : Int64)...3).toList = [1, 2] := by native_decide
example : ((-1 : Int64)...3).toList = [-1, 0, 1, 2] := by native_decide
example : ((1 : Int64)...=3).toList = [1, 2, 3] := by native_decide
example : ((-4 : Int64)...-1).toList = [-4, -3, -2] := by native_decide
example : ((2 ^ 63 - 1 : Int64)...(2 ^ 63)).toList = [] := by native_decide
example : (*...Int64.minValue + 1).toList = [Int64.minValue] := by native_decide
example : (Int64.maxValue...*).toList = [Int64.maxValue] := by native_decide
example : (*...* : Std.Rii Int64).size = 2 ^ 64 := by native_decide

example : ((1 : ISize)...3).toList = [1, 2] := by native_decide
example : ((-1 : ISize)...3).toList = [-1, 0, 1, 2] := by native_decide
example : ((1 : ISize)...=3).toList = [1, 2, 3] := by native_decide
example : ((-4 : ISize)...-1).toList = [-4, -3, -2] := by native_decide
example : (*...ISize.minValue + 1).toList = [ISize.minValue] := by native_decide
example : (ISize.maxValue...*).toList = [ISize.maxValue] := by native_decide
example : (*...* : Std.Rii ISize).size = 2 ^ System.Platform.numBits := by native_decide

end SInt
