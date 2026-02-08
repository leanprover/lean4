import Std.Data.Iterators

example : #[1, 2, 3][*...*].toList = [1, 2, 3] := by simp
example : #[1, 2, 3][*...2].toList = [1, 2] := by simp
example : #[1, 2, 3][*...<2].toList = [1, 2] := by simp
example : #[1, 2, 3][*...=1].toList = [1, 2] := by simp
example : #[1, 2, 3][0<...*].toList = [2, 3] := by simp
example : #[1, 2, 3][0<...2].toList = [2] := by simp
example : #[1, 2, 3][0<...<2].toList = [2] := by simp
example : #[1, 2, 3][0<...=1].toList = [2] := by simp
example : #[1, 2, 3][1...*].toList = [2, 3] := by simp
example : #[1, 2, 3][1...2].toList = [2] := by simp
example : #[1, 2, 3][1...<2].toList = [2] := by simp
example : #[1, 2, 3][1...=1].toList = [2] := by simp
example : #[1, 2, 3][*...*].toArray = #[1, 2, 3] := by simp
example : #[1, 2, 3][*...2].toArray = #[1, 2] := by simp
example : #[1, 2, 3][*...<2].toArray = #[1, 2] := by simp
example : #[1, 2, 3][*...=1].toArray = #[1, 2] := by simp
example : #[1, 2, 3][0<...*].toArray = #[2, 3] := by simp
example : #[1, 2, 3][0<...2].toArray = #[2] := by simp
example : #[1, 2, 3][0<...<2].toArray = #[2] := by simp
example : #[1, 2, 3][0<...=1].toArray = #[2] := by simp
example : #[1, 2, 3][1...*].toArray = #[2, 3] := by simp
example : #[1, 2, 3][1...2].toArray = #[2] := by simp
example : #[1, 2, 3][1...<2].toArray = #[2] := by simp
example : #[1, 2, 3][1...=1].toArray = #[2] := by simp
example : (#[1, 2, 3][1...*].take 1).toList = [2] := by native_decide

example : #[1, 2, 3][1...<10].size = 2 := by simp
example : #[1, 1, 1][0...2].size = 2 := by simp

-- Verify that subarray iterators are universe polymorphic
def f (_ : Type) : Nat := 1
example : #[Nat, Int][*...1].toList.map f = [1] := by simp [f]

example : #[1, 2, 3][0...2][1...2].toList = [2] := by simp
example : #[1, 2, 3][0...2][1...5].toList = [2] := by simp
example : #[1, 2, 3][1...2][0...2].toList = [2] := by simp
example : #[1, 2, 3][1...2][1...2].toList = [] := by simp
example : #[1, 2, 3][1...2][0...=1].toList = [2] := by simp
example : #[1, 2, 3][1...*][1...*].toList = [3] := by simp
example : #[1, 2, 3, 4, 5][1...*][0<...2].toList = [3] := by simp
example : #[1, 2, 3, 4, 5][1...*][0<...=2].toList = [3, 4] := by simp
example : #[1, 2, 3, 4, 5][1...*][0<...*].toList = [3, 4, 5] := by simp
example : #[1, 2, 3, 4, 5][1...3][0<...*].toList = [3] := by simp
example : #[1, 2, 3, 4, 5][1...*][*...2].toList = [2, 3] := by simp
example : #[1, 2, 3, 4, 5][1...*][*...=2].toList = [2, 3, 4] := by simp
example : #[1, 2, 3, 4, 5][1...*][*...*].toList = [2, 3, 4, 5] := by simp
example : #[1, 2, 3][0...2][*...*].toList = [1, 2] := by simp
example : #[1, 2, 3][0...2][1...2].toArray = #[2] := by simp
example : #[1, 2, 3][0...2][1...5].toArray = #[2] := by simp
example : #[1, 2, 3][1...2][0...2].toArray = #[2] := by simp
example : #[1, 2, 3][1...2][1...2].toArray = #[] := by simp
example : #[1, 2, 3][1...2][0...=1].toArray = #[2] := by simp
example : #[1, 2, 3][1...*][1...*].toArray = #[3] := by simp
example : #[1, 2, 3, 4, 5][1...*][0<...2].toArray = #[3] := by simp
example : #[1, 2, 3, 4, 5][1...*][0<...=2].toArray = #[3, 4] := by simp
example : #[1, 2, 3, 4, 5][1...*][0<...*].toArray = #[3, 4, 5] := by simp
example : #[1, 2, 3, 4, 5][1...3][0<...*].toArray = #[3] := by simp
example : #[1, 2, 3, 4, 5][1...*][*...2].toArray = #[2, 3] := by simp
example : #[1, 2, 3, 4, 5][1...*][*...=2].toArray = #[2, 3, 4] := by simp
example : #[1, 2, 3, 4, 5][1...*][*...*].toArray = #[2, 3, 4, 5] := by simp
example : #[1, 2, 3][0...2][*...*].toArray = #[1, 2] := by simp

example : [1, 2, 3][*...*].toList = [1, 2, 3] := by simp
example : [1, 2, 3][*...2].toList = [1, 2] := by simp
example : [1, 2, 3][*...<2].toList = [1, 2] := by simp
example : [1, 2, 3][*...=1].toList = [1, 2] := by simp
example : [1, 2, 3][0<...*].toList = [2, 3] := by simp
example : [1, 2, 3][0<...2].toList = [2] := by simp
example : [1, 2, 3][0<...<2].toList = [2] := by simp
example : [1, 2, 3][0<...=1].toList = [2] := by simp
example : [1, 2, 3][1...*].toList = [2, 3] := by simp
example : [1, 2, 3][1...2].toList = [2] := by simp
example : [1, 2, 3][1...<2].toList = [2] := by simp
example : [1, 2, 3][1...=1].toList = [2] := by simp
example : [1, 2, 3][*...*].toArray = #[1, 2, 3] := by simp
example : [1, 2, 3][*...2].toArray = #[1, 2] := by simp
example : [1, 2, 3][*...<2].toArray = #[1, 2] := by simp
example : [1, 2, 3][*...=1].toArray = #[1, 2] := by simp
example : [1, 2, 3][0<...*].toArray = #[2, 3] := by simp
example : [1, 2, 3][0<...2].toArray = #[2] := by simp
example : [1, 2, 3][0<...<2].toArray = #[2] := by simp
example : [1, 2, 3][0<...=1].toArray = #[2] := by simp
example : [1, 2, 3][1...*].toArray = #[2, 3] := by simp
example : [1, 2, 3][1...2].toArray = #[2] := by simp
example : [1, 2, 3][1...<2].toArray = #[2] := by simp
example : [1, 2, 3][1...=1].toArray = #[2] := by simp

example : [1, 2, 3][1...<10].size = 2 := by simp
example : [1, 1, 1][0...2].size = 2 := by simp

-- Verify that list slice iterators are universe polymorphic
example : [Nat, Int][*...1].toList.map f = [1] := by simp [f]

example : [1, 2, 3][0...2][1...2].toList = [2] := by simp
example : [1, 2, 3][0...2][1...5].toList = [2] := by simp
example : [1, 2, 3][1...2][0...2].toList = [2] := by simp
example : [1, 2, 3][1...2][1...2].toList = [] := by simp
example : [1, 2, 3][1...2][0...=1].toList = [2] := by simp
example : [1, 2, 3][1...*][1...*].toList = [3] := by simp
example : [1, 2, 3, 4, 5][1...*][0<...2].toList = [3] := by simp
example : [1, 2, 3, 4, 5][1...*][0<...=2].toList = [3, 4] := by simp
example : [1, 2, 3, 4, 5][1...*][0<...*].toList = [3, 4, 5] := by simp
example : [1, 2, 3, 4, 5][1...3][0<...*].toList = [3] := by simp
example : [1, 2, 3, 4, 5][1...*][*...2].toList = [2, 3] := by simp
example : [1, 2, 3, 4, 5][1...*][*...=2].toList = [2, 3, 4] := by simp
example : [1, 2, 3, 4, 5][1...*][*...*].toList = [2, 3, 4, 5] := by simp
example : [1, 2, 3][0...2][*...*].toList = [1, 2] := by simp
example : [1, 2, 3][0...2][1...2].toArray = #[2] := by simp
example : [1, 2, 3][0...2][1...5].toArray = #[2] := by simp
example : [1, 2, 3][1...2][0...2].toArray = #[2] := by simp
example : [1, 2, 3][1...2][1...2].toArray = #[] := by simp
example : [1, 2, 3][1...2][0...=1].toArray = #[2] := by simp
example : [1, 2, 3][1...*][1...*].toArray = #[3] := by simp
example : [1, 2, 3, 4, 5][1...*][0<...2].toArray = #[3] := by simp
example : [1, 2, 3, 4, 5][1...*][0<...=2].toArray = #[3, 4] := by simp
example : [1, 2, 3, 4, 5][1...*][0<...*].toArray = #[3, 4, 5] := by simp
example : [1, 2, 3, 4, 5][1...3][0<...*].toArray = #[3] := by simp
example : [1, 2, 3, 4, 5][1...*][*...2].toArray = #[2, 3] := by simp
example : [1, 2, 3, 4, 5][1...*][*...=2].toArray = #[2, 3, 4] := by simp
example : [1, 2, 3, 4, 5][1...*][*...*].toArray = #[2, 3, 4, 5] := by simp
example : [1, 2, 3][0...2][*...*].toArray = #[1, 2] := by simp

example (xs : List α) : xs[*...5].size = xs[0...5].size := by
  grind

example {xs : List α} {lo hi : Nat} :
    xs[lo...=hi].toList = (xs.take (hi + 1)).drop lo := by
  grind

-- verify that grind is powerful enough to prove some lemmas that are not grind-annotated
example : type_of% @List.toList_mkSlice_rcc := by grind
example : type_of% @List.toArray_mkSlice_rcc := by grind
example : type_of% @List.size_mkSlice_rcc := by grind
example : type_of% @List.toList_mkSlice_rci := by grind
example : type_of% @List.toArray_mkSlice_rci := by grind
example : type_of% @List.toArray_mkSlice_roi := by grind
example : type_of% @List.toArray_mkSlice_ric := by grind
example : type_of% @List.toArray_mkSlice_rii_eq_toArray_mkSlice_rco := by grind
example : type_of% @List.toArray_mkSlice_roc := by grind
example : type_of% @List.toList_mkSlice_ric := by grind

example (xs : List Nat) : xs[1...=4][2...3].toList = xs[3...4].toList := by
  grind [List.take_drop, List.drop_drop]

example : type_of% @Array.toArray_mkSlice_rcc := by grind
example : type_of% @Array.toArray_mkSlice_rcc := by grind
example : type_of% @Array.size_mkSlice_rcc := by grind
example : type_of% @Array.toArray_mkSlice_rci := by grind
example : type_of% @Array.toArray_mkSlice_rci := by grind
example : type_of% @Array.toArray_mkSlice_roi := by grind
example : type_of% @Array.toArray_mkSlice_ric := by grind
example : type_of% @Array.toArray_mkSlice_roc := by grind
example : type_of% @Array.toArray_mkSlice_ric := by grind

example (xs : Array Nat) : xs[1...=4][2...3].toList = xs[3...4].toList := by
  grind [List.take_drop, List.drop_drop]

example (xs : Array Nat) : xs[1...=4][2...3].toArray = xs[3...4].toArray := by grind
