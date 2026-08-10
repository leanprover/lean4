module
import all Init.Data.Array.QSort.Basic
import all Init.Data.Array.Basic
import Std

-- Basic indexing
theorem test1 : #[1, 2, 3][0] = 1 := by cbv

theorem test2 : #[1, 2, 3][2] = 3 := by cbv

-- Optional indexing (in bounds)
theorem test3 : #[1, 2, 3][1]? = some 2 := by cbv

-- Optional indexing (out of bounds)
theorem test4 : #[1, 2, 3][5]? = none := by cbv

-- Nested arrays
theorem test5 : #[#[1, 2], #[3, 4]][1][0] = 3 := by cbv

-- Array of strings/other types
theorem test6 : #["a", "b", "c"][0] = "a" := by cbv

theorem testSize : #[a, b, c].size = 3 := by cbv

theorem testPush : #[a, b, c].push d = #[a, b, c, d] := by cbv

def range (n : Nat) : Array Nat :=
  match n with
  | 0 => #[]
  | k + 1 => (range k).push k

def rangeReverse (n : Nat) (acc : Array Nat) : Array Nat :=
  match n with
  | 0 => acc
  | k + 1 => rangeReverse k (acc.push k)

set_option maxRecDepth 0
set_option cbv.maxSteps 10000000

theorem testRange : (range 2000).size = 2000 := by cbv

theorem testReplicate : (Array.replicate (3 ^ 27) 0).size = 3 ^ 27 := by cbv

theorem testSet : #[0, 1, 2, 3, 4].set 2 24 = #[0, 1, 24, 3, 4] := by cbv

theorem testSetIfInBounds : #[0, 1, 2, 3, 4].setIfInBounds 2 24 = #[0, 1, 24, 3, 4] := by cbv

theorem testModify : #[0, 1, 2, 3, 4].modify 2 (fun n => n + 22) = #[0, 1, 24, 3, 4] := by cbv

theorem testMap : #[0, 1, 2, 3, 4].map (fun n => n + 22) = #[22, 23, 24, 25, 26] := by cbv

theorem testMapGeneralized : #[0, 1, 2, 3, 4].map f = #[f 0, f 1, f 2, f 3, f 4] := by cbv

theorem testMapReplicate : (Array.replicate (3 ^ 27) 0).map (· + 1) = Array.replicate (3 ^ 27) 1 := by cbv

theorem testMapReplicateSet :
    (Array.replicate (3 ^ 27) 0 |>.set! 1874317 90).map (· + 1) =
      (Array.replicate (3 ^ 27) 1).set! 1874317 91 := by cbv

def doMatch (x : Array Nat) : List Nat :=
  match x with
  | ⟨l⟩ => 3 :: l

theorem testToList : (range 20).toList = List.range 20 := by cbv

theorem testToList' : doMatch (range 20) = 3 :: List.range 20 := by cbv

theorem testGet!Replicate : (Array.replicate (3 ^ 27) 0)[231489]! = 0 := by cbv

theorem testGet?Replicate : (Array.replicate (3 ^ 27) 0)[231489]? = some 0 := by cbv

theorem testGetReplicate : (Array.replicate (3 ^ 27) 0)[231489]'(by simp) = 0 := by cbv

theorem testQSort : Array.qsort #[1, 8, 3, 2, 9, 0, 7, 13, 0, 0] = #[0, 0, 0, 1, 2, 3, 7, 8, 9, 13] := by cbv

theorem testReverse : Array.reverse #[1, 2, 3, 4, 5] = #[5, 4, 3, 2, 1] := by cbv

--theorem testQSortRange : Array.qsort (rangeReverse 300 #[]) = range 300 := by cbv

theorem testFoldl : (range 1000).foldr (· + ·) 0 = 499500 := by cbv

theorem testFoldlReplicate : (Array.replicate (3 ^ 27) 3).foldl (· + ·) 0 200 1200 = 3000 := by cbv

theorem testBEq : range 5000 == range 5000 := by cbv
