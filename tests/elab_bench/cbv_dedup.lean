import Std

def dedup (l : List Nat) : List Nat := Id.run do
  let mut S : Std.TreeSet Nat := ∅
  for i in l do
    S := S.insert i
  return S.toList

example : dedup [1] = [1] := by conv => lhs; cbv

example : dedup [1,2] = [1,2] := by conv => lhs; cbv

example : dedup [1,1] = [1] := by conv => lhs; cbv

example : dedup [1,2,2] = [1,2] := by conv => lhs; cbv
