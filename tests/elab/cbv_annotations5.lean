module

import Std.Data.Iterators

@[grind =]
def makeAPile₁ (n : Nat) : List Nat :=
  (*...n).iter.map (n + 2 * ·) |>.toList

@[grind =]
def makeAPile₂ (n : Nat) : List Nat :=
  (*...n).iter.map (fun i => n + 2 * (n - 1 - i)) |>.toListRev

example : makeAPile₁ 0 = [] := by cbv
example : makeAPile₁ 1 = [1] := by cbv
example : makeAPile₁ 2 = [2, 4] := by cbv
example : makeAPile₁ 3 = [3, 5, 7] := by cbv
example : makeAPile₁ 4 = [4, 6, 8, 10] := by cbv
example : makeAPile₁ 5 = [5, 7, 9, 11, 13] := by cbv
example : makeAPile₁ 6 = [6, 8, 10, 12, 14, 16] := by cbv
example : makeAPile₁ 8 = [8, 10, 12, 14, 16, 18, 20, 22] := by cbv

example : makeAPile₂ 0 = [] := by cbv
example : makeAPile₂ 1 = [1] := by cbv
example : makeAPile₂ 2 = [2, 4] := by cbv
example : makeAPile₂ 3 = [3, 5, 7] := by cbv
example : makeAPile₂ 4 = [4, 6, 8, 10] := by cbv
example : makeAPile₂ 5 = [5, 7, 9, 11, 13] := by cbv
example : makeAPile₂ 6 = [6, 8, 10, 12, 14, 16] := by cbv
example : makeAPile₂ 8 = [8, 10, 12, 14, 16, 18, 20, 22] := by cbv
