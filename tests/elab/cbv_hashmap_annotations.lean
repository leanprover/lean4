import Std
open Std

/-! ### HashSet.contains -/

example : (HashSet.emptyWithCapacity.insert 3).contains 3 = true := by cbv
example : (HashSet.emptyWithCapacity.insert 3).contains 4 = false := by cbv
example : (HashSet.emptyWithCapacity : HashSet Nat).contains 1 = false := by cbv
example : (HashSet.emptyWithCapacity.insert 1 |>.insert 2 |>.insert 3).contains 2 = true := by cbv
example : (HashSet.emptyWithCapacity.insert 1 |>.insert 2 |>.insert 3).contains 5 = false := by cbv
example : (HashSet.emptyWithCapacity.insert 10 |>.insert 20).contains 10 = true := by cbv
example : (HashSet.emptyWithCapacity.insert 10 |>.insert 20).contains 20 = true := by cbv
example : (HashSet.emptyWithCapacity.insert 10 |>.insert 20).contains 30 = false := by cbv

/-! ### HashMap.contains -/

example : ((HashMap.emptyWithCapacity : HashMap Nat Nat).insert 1 10).contains 1 = true := by cbv
example : ((HashMap.emptyWithCapacity : HashMap Nat Nat).insert 1 10).contains 2 = false := by cbv
example : (HashMap.emptyWithCapacity : HashMap Nat Nat).contains 1 = false := by cbv
example : ((HashMap.emptyWithCapacity : HashMap Nat Nat).insert 1 10 |>.insert 2 20 |>.insert 3 30).contains 2 = true := by cbv
example : ((HashMap.emptyWithCapacity : HashMap Nat Nat).insert 1 10 |>.insert 2 20 |>.insert 3 30).contains 4 = false := by cbv

/-! ### HashMap.get? -/

example : ((HashMap.emptyWithCapacity : HashMap Nat Nat).insert 1 2).get? 1 = .some 2 := by cbv
example : ((HashMap.emptyWithCapacity : HashMap Nat Nat).insert 1 2).get? 3 = .none := by cbv
example : (HashMap.emptyWithCapacity : HashMap Nat Nat).get? 1 = .none := by cbv
example : ((HashMap.emptyWithCapacity : HashMap Nat Nat).insert 1 10 |>.insert 2 20 |>.insert 3 30).get? 1 = .some 10 := by cbv
example : ((HashMap.emptyWithCapacity : HashMap Nat Nat).insert 1 10 |>.insert 2 20 |>.insert 3 30).get? 2 = .some 20 := by cbv
example : ((HashMap.emptyWithCapacity : HashMap Nat Nat).insert 1 10 |>.insert 2 20 |>.insert 3 30).get? 3 = .some 30 := by cbv
example : ((HashMap.emptyWithCapacity : HashMap Nat Nat).insert 1 10 |>.insert 2 20 |>.insert 3 30).get? 4 = .none := by cbv
-- overwrite
example : ((HashMap.emptyWithCapacity : HashMap Nat Nat).insert 1 10 |>.insert 1 99).get? 1 = .some 99 := by cbv

/-! ### HashMap.get! -/

example : ((HashMap.emptyWithCapacity : HashMap Nat Nat).insert 1 42).get! 1 = 42 := by cbv
example : ((HashMap.emptyWithCapacity : HashMap Nat Nat).insert 1 42).get! 2 = 0 := by cbv
example : (HashMap.emptyWithCapacity : HashMap Nat Nat).get! 1 = 0 := by cbv
example : ((HashMap.emptyWithCapacity : HashMap Nat Nat).insert 1 10 |>.insert 2 20).get! 2 = 20 := by cbv
example : ((HashMap.emptyWithCapacity : HashMap Nat Nat).insert 1 10 |>.insert 2 20).get! 3 = 0 := by cbv

/-! ### HashMap.getD -/

example : ((HashMap.emptyWithCapacity : HashMap Nat Nat).insert 1 42).getD 1 999 = 42 := by cbv
example : ((HashMap.emptyWithCapacity : HashMap Nat Nat).insert 1 42).getD 2 999 = 999 := by cbv
example : (HashMap.emptyWithCapacity : HashMap Nat Nat).getD 1 999 = 999 := by cbv
example : ((HashMap.emptyWithCapacity : HashMap Nat Nat).insert 1 10 |>.insert 2 20).getD 2 0 = 20 := by cbv
example : ((HashMap.emptyWithCapacity : HashMap Nat Nat).insert 1 10 |>.insert 2 20).getD 3 0 = 0 := by cbv

/-! ### DHashMap.contains -/

example : ((DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).insert 1 10).contains 1 = true := by cbv
example : ((DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).insert 1 10).contains 2 = false := by cbv
example : (DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).contains 1 = false := by cbv
example : ((DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).insert 1 10 |>.insert 2 20 |>.insert 3 30).contains 2 = true := by cbv
example : ((DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).insert 1 10 |>.insert 2 20 |>.insert 3 30).contains 4 = false := by cbv

/-! ### DHashMap.get? -/

example : ((DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).insert 1 2).get? 1 = .some 2 := by cbv
example : ((DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).insert 1 2).get? 3 = .none := by cbv
example : (DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).get? 1 = .none := by cbv
example : ((DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).insert 1 10 |>.insert 2 20 |>.insert 3 30).get? 1 = .some 10 := by cbv
example : ((DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).insert 1 10 |>.insert 2 20 |>.insert 3 30).get? 2 = .some 20 := by cbv
example : ((DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).insert 1 10 |>.insert 2 20 |>.insert 3 30).get? 4 = .none := by cbv
-- overwrite
example : ((DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).insert 1 10 |>.insert 1 99).get? 1 = .some 99 := by cbv

/-! ### DHashMap.get! -/

example : ((DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).insert 1 42).get! 1 = 42 := by cbv
example : ((DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).insert 1 42).get! 2 = 0 := by cbv
example : (DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).get! 1 = 0 := by cbv

/-! ### DHashMap.getD -/

example : ((DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).insert 1 42).getD 1 999 = 42 := by cbv
example : ((DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).insert 1 42).getD 2 999 = 999 := by cbv
example : (DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).getD 1 999 = 999 := by cbv

/-! ### HashSet.erase -/

-- erase from empty
example : ((HashSet.emptyWithCapacity : HashSet Nat).erase 1).contains 1 = false := by cbv
-- erase existing element
example : ((HashSet.emptyWithCapacity.insert 1 |>.insert 2 |>.insert 3).erase 2).contains 2 = false := by cbv
-- erase does not affect other elements
example : ((HashSet.emptyWithCapacity.insert 1 |>.insert 2 |>.insert 3).erase 2).contains 1 = true := by cbv
example : ((HashSet.emptyWithCapacity.insert 1 |>.insert 2 |>.insert 3).erase 2).contains 3 = true := by cbv
-- erase non-existing element
example : ((HashSet.emptyWithCapacity.insert 1 |>.insert 2).erase 5).contains 1 = true := by cbv
example : ((HashSet.emptyWithCapacity.insert 1 |>.insert 2).erase 5).contains 5 = false := by cbv

/-! ### HashMap.erase + contains -/

example : ((HashMap.emptyWithCapacity : HashMap Nat Nat).erase 1).contains 1 = false := by cbv
example : ((HashMap.emptyWithCapacity : HashMap Nat Nat).insert 1 10 |>.insert 2 20 |>.erase 1).contains 1 = false := by cbv
example : ((HashMap.emptyWithCapacity : HashMap Nat Nat).insert 1 10 |>.insert 2 20 |>.erase 1).contains 2 = true := by cbv

/-! ### HashMap.erase + get? -/

example : ((HashMap.emptyWithCapacity : HashMap Nat Nat).insert 1 10 |>.insert 2 20 |>.erase 1).get? 1 = .none := by cbv
example : ((HashMap.emptyWithCapacity : HashMap Nat Nat).insert 1 10 |>.insert 2 20 |>.erase 1).get? 2 = .some 20 := by cbv
example : ((HashMap.emptyWithCapacity : HashMap Nat Nat).erase 1).get? 1 = .none := by cbv

/-! ### HashMap.erase + get! -/

example : ((HashMap.emptyWithCapacity : HashMap Nat Nat).insert 1 10 |>.insert 2 20 |>.erase 1).get! 1 = 0 := by cbv
example : ((HashMap.emptyWithCapacity : HashMap Nat Nat).insert 1 10 |>.insert 2 20 |>.erase 1).get! 2 = 20 := by cbv

/-! ### HashMap.erase + getD -/

example : ((HashMap.emptyWithCapacity : HashMap Nat Nat).insert 1 10 |>.insert 2 20 |>.erase 1).getD 1 999 = 999 := by cbv
example : ((HashMap.emptyWithCapacity : HashMap Nat Nat).insert 1 10 |>.insert 2 20 |>.erase 1).getD 2 999 = 20 := by cbv

/-! ### DHashMap.erase + contains -/

example : ((DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).erase 1).contains 1 = false := by cbv
example : ((DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).insert 1 10 |>.insert 2 20 |>.erase 1).contains 1 = false := by cbv
example : ((DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).insert 1 10 |>.insert 2 20 |>.erase 1).contains 2 = true := by cbv

/-! ### DHashMap.erase + get? -/

example : ((DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).insert 1 10 |>.insert 2 20 |>.erase 1).get? 1 = .none := by cbv
example : ((DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).insert 1 10 |>.insert 2 20 |>.erase 1).get? 2 = .some 20 := by cbv

/-! ### DHashMap.erase + get! -/

example : ((DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).insert 1 10 |>.insert 2 20 |>.erase 1).get! 1 = 0 := by cbv
example : ((DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).insert 1 10 |>.insert 2 20 |>.erase 1).get! 2 = 20 := by cbv

/-! ### DHashMap.erase + getD -/

example : ((DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).insert 1 10 |>.insert 2 20 |>.erase 1).getD 1 999 = 999 := by cbv
example : ((DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).insert 1 10 |>.insert 2 20 |>.erase 1).getD 2 999 = 20 := by cbv

/-! ### HashMap.map + getD -/

example : ((HashMap.emptyWithCapacity : HashMap Nat Nat).insert 1 10 |>.insert 2 20 |>.map (fun _ v => v * 2)).getD 1 999 = 20 := by cbv
example : ((HashMap.emptyWithCapacity : HashMap Nat Nat).insert 1 10 |>.insert 2 20 |>.map (fun _ v => v * 2)).getD 2 999 = 40 := by cbv
example : ((HashMap.emptyWithCapacity : HashMap Nat Nat).insert 1 10 |>.insert 2 20 |>.map (fun _ v => v * 2)).getD 3 999 = 999 := by cbv
example : ((HashMap.emptyWithCapacity : HashMap Nat Nat).map (fun _ v => v + 1)).getD 1 999 = 999 := by cbv

/-! ### HashMap.map + contains -/

example : ((HashMap.emptyWithCapacity : HashMap Nat Nat).insert 1 10 |>.insert 2 20 |>.map (fun _ v => v * 2)).contains 1 = true := by cbv
example : ((HashMap.emptyWithCapacity : HashMap Nat Nat).insert 1 10 |>.insert 2 20 |>.map (fun _ v => v * 2)).contains 3 = false := by cbv

/-! ### HashMap.filter + getD -/

example : ((HashMap.emptyWithCapacity : HashMap Nat Nat).insert 1 10 |>.insert 2 20 |>.insert 3 5 |>.filter (fun _ v => v > 8)).getD 1 999 = 10 := by cbv
example : ((HashMap.emptyWithCapacity : HashMap Nat Nat).insert 1 10 |>.insert 2 20 |>.insert 3 5 |>.filter (fun _ v => v > 8)).getD 3 999 = 999 := by cbv
example : ((HashMap.emptyWithCapacity : HashMap Nat Nat).insert 1 10 |>.insert 2 20 |>.insert 3 5 |>.filter (fun _ v => v > 8)).getD 4 999 = 999 := by cbv
example : ((HashMap.emptyWithCapacity : HashMap Nat Nat).insert 1 10 |>.insert 2 20 |>.filter (fun _ v => v > 15)).getD 2 999 = 20 := by cbv
example : ((HashMap.emptyWithCapacity : HashMap Nat Nat).insert 1 10 |>.insert 2 20 |>.filter (fun _ v => v > 15)).getD 1 999 = 999 := by cbv

/-! ### HashMap.filterMap + getD -/

example : ((HashMap.emptyWithCapacity : HashMap Nat Nat).insert 1 10 |>.insert 2 20 |>.filterMap (fun _ v => if v > 15 then some (v * 2) else none)).getD 2 999 = 40 := by cbv
example : ((HashMap.emptyWithCapacity : HashMap Nat Nat).insert 1 10 |>.insert 2 20 |>.filterMap (fun _ v => if v > 15 then some (v * 2) else none)).getD 1 999 = 999 := by cbv
example : ((HashMap.emptyWithCapacity : HashMap Nat Nat).insert 1 10 |>.insert 2 20 |>.filterMap (fun _ v => if v > 15 then some (v * 2) else none)).getD 3 999 = 999 := by cbv

/-! ### DHashMap.map + get? -/

example : ((DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).insert 1 10 |>.insert 2 20 |>.map (fun _ v => v * 2)).get? 1 = .some 20 := by cbv
example : ((DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).insert 1 10 |>.insert 2 20 |>.map (fun _ v => v * 2)).get? 2 = .some 40 := by cbv
example : ((DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).insert 1 10 |>.insert 2 20 |>.map (fun _ v => v * 2)).get? 3 = .none := by cbv

/-! ### DHashMap.map + get! -/

example : ((DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).insert 1 10 |>.insert 2 20 |>.map (fun _ v => v + 1)).get! 1 = 11 := by cbv
example : ((DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).insert 1 10 |>.insert 2 20 |>.map (fun _ v => v + 1)).get! 3 = 0 := by cbv

/-! ### DHashMap.map + getD -/

example : ((DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).insert 1 10 |>.map (fun _ v => v + 5)).getD 1 999 = 15 := by cbv
example : ((DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).insert 1 10 |>.map (fun _ v => v + 5)).getD 2 999 = 999 := by cbv

/-! ### DHashMap.map + contains -/

example : ((DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).insert 1 10 |>.insert 2 20 |>.map (fun _ v => v * 2)).contains 1 = true := by cbv
example : ((DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).insert 1 10 |>.insert 2 20 |>.map (fun _ v => v * 2)).contains 3 = false := by cbv

/-! ### DHashMap.filter + contains -/

example : ((DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).insert 1 10 |>.insert 2 20 |>.filter (fun _ v => v > 15)).contains 2 = true := by cbv
example : ((DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).insert 1 10 |>.insert 2 20 |>.filter (fun _ v => v > 15)).contains 1 = false := by cbv

/-! ### DHashMap.filter + get? -/

example : ((DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).insert 1 10 |>.insert 2 20 |>.insert 3 5 |>.filter (fun _ v => v > 8)).get? 1 = .some 10 := by cbv
example : ((DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).insert 1 10 |>.insert 2 20 |>.insert 3 5 |>.filter (fun _ v => v > 8)).get? 3 = .none := by cbv

/-! ### DHashMap.filter + get! -/

example : ((DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).insert 1 10 |>.insert 2 20 |>.filter (fun _ v => v > 15)).get! 2 = 20 := by cbv
example : ((DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).insert 1 10 |>.insert 2 20 |>.filter (fun _ v => v > 15)).get! 1 = 0 := by cbv

/-! ### DHashMap.filter + getD -/

example : ((DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).insert 1 10 |>.insert 2 20 |>.filter (fun _ v => v > 15)).getD 2 999 = 20 := by cbv
example : ((DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).insert 1 10 |>.insert 2 20 |>.filter (fun _ v => v > 15)).getD 1 999 = 999 := by cbv

/-! ### DHashMap.filterMap + get? -/

example : ((DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).insert 1 10 |>.insert 2 20 |>.filterMap (fun _ v => if v > 15 then some (v * 2) else none)).get? 2 = .some 40 := by cbv
example : ((DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).insert 1 10 |>.insert 2 20 |>.filterMap (fun _ v => if v > 15 then some (v * 2) else none)).get? 1 = .none := by cbv

/-! ### DHashMap.filterMap + get! -/

example : ((DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).insert 1 10 |>.insert 2 20 |>.filterMap (fun _ v => if v > 15 then some (v * 2) else none)).get! 2 = 40 := by cbv
example : ((DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).insert 1 10 |>.insert 2 20 |>.filterMap (fun _ v => if v > 15 then some (v * 2) else none)).get! 1 = 0 := by cbv

/-! ### DHashMap.filterMap + getD -/

example : ((DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).insert 1 10 |>.insert 2 20 |>.filterMap (fun _ v => if v > 15 then some (v * 2) else none)).getD 2 999 = 40 := by cbv
example : ((DHashMap.emptyWithCapacity : DHashMap Nat (fun _ => Nat)).insert 1 10 |>.insert 2 20 |>.filterMap (fun _ v => if v > 15 then some (v * 2) else none)).getD 1 999 = 999 := by cbv
