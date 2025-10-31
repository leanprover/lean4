import Std.Data.Iterators

example : #[1, 2, 3][*...*].toList = [1, 2, 3] := by native_decide

example : #[1, 2, 3][*...2].toList = [1, 2] := by native_decide

example : #[1, 2, 3][*...<2].toList = [1, 2] := by native_decide

example : #[1, 2, 3][*...=1].toList = [1, 2] := by native_decide

example : #[1, 2, 3][0<...*].toList = [2, 3] := by native_decide

example : #[1, 2, 3][0<...2].toList = [2] := by native_decide

example : #[1, 2, 3][0<...<2].toList = [2] := by native_decide

example : #[1, 2, 3][0<...=1].toList = [2] := by native_decide

example : #[1, 2, 3][1...*].toList = [2, 3] := by native_decide

example : #[1, 2, 3][1...2].toList = [2] := by native_decide

example : #[1, 2, 3][1...<2].toList = [2] := by native_decide

example : #[1, 2, 3][1...=1].toList = [2] := by native_decide

example : #[1, 2, 3][1...<10].size = 2 := by native_decide

example : (#[1, 2, 3][1...*].take 1).toList = [2] := by native_decide

example : #[1, 1, 1][0...2].size = 2 := by native_decide

-- Verify that subarray iterators are universe polymorphic
def f (_ : Type) : Nat := 1
example : #[Nat, Int][*...1].toList.map f = [1] := by native_decide


example : [1, 2, 3][*...*].toList = [1, 2, 3] := by native_decide

example : [1, 2, 3][*...2].toList = [1, 2] := by native_decide

example : [1, 2, 3][*...<2].toList = [1, 2] := by native_decide

example : [1, 2, 3][*...=1].toList = [1, 2] := by native_decide

example : [1, 2, 3][0<...*].toList = [2, 3] := by native_decide

example : [1, 2, 3][0<...2].toList = [2] := by native_decide

example : [1, 2, 3][0<...<2].toList = [2] := by native_decide

example : [1, 2, 3][0<...=1].toList = [2] := by native_decide

example : [1, 2, 3][1...*].toList = [2, 3] := by native_decide

example : [1, 2, 3][1...2].toList = [2] := by native_decide

example : [1, 2, 3][1...<2].toList = [2] := by native_decide

example : [1, 2, 3][1...=1].toList = [2] := by native_decide

example : [1, 2, 3][1...<10].size = 2 := by native_decide

example : [1, 1, 1][0...2].size = 2 := by native_decide

-- Verify that list slice iterators are universe polymorphic
example : [Nat, Int][*...1].toList.map f = [1] := by native_decide
