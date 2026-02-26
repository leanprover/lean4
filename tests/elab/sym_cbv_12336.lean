import Std
set_option cbv.warning false

def test : ((Std.TreeSet.empty : Std.TreeSet Nat).insertMany [1]).toList = [1] := by
  conv => lhs; cbv
