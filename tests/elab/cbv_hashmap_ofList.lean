import Std

open Std

attribute [cbv_opaque] HashMap.insert HashMap.emptyWithCapacity

example : ((HashMap.ofList [] : HashMap String Nat) |>.get? "1") = .none := by
  cbv

example : ((HashMap.ofArray #[] : HashMap String Nat) |>.get? "1") = .none := by
  cbv

example : (Std.HashMap.ofList [("1", 1)] |>.get? "1") = some 1 := by
  cbv

example : (Std.HashMap.ofList [("1", 1), ("2", 2)] |>.get? "2") = some 2 := by
  cbv

example : (Std.HashMap.ofArray #[("1", 1), ("2", 2)] |>.get? "2") = some 2 := by
  cbv

example : ((HashSet.ofList [] : HashSet String) |>.contains "1") = false := by
  cbv

example : ((HashSet.ofList ["2","1"] : HashSet String) |>.contains "1") = true := by
  cbv
