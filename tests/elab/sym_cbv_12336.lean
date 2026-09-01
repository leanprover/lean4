import Std

def test : ((Std.TreeSet.empty : Std.TreeSet Nat).insertMany [1]).toList = [1] := by
  conv => lhs; cbv
