import SimplcLean._root_

-- I don't understand this next set: `simp` seems to close the goal.
example {α : Type _} [BEq α] [EquivBEq α] (a : α) : (a == a) = true := by simp
example {α : Type _} {β : Type _} [BEq α] [Hashable α] {m : Std.HashMap α β}
    [LawfulHashable α] {a : α} {_ : β} [EquivBEq α] [LawfulHashable α] :
    (a == a) = true ∨ a ∈ m :=
  by simp

simp_lc whitelist Std.HashSet.contains_insert_self Std.HashSet.contains_insert
simp_lc whitelist Std.HashSet.mem_insert Std.HashSet.mem_insert_self
simp_lc whitelist Std.HashMap.mem_insert_self Std.HashMap.mem_insert
simp_lc whitelist Std.DHashMap.mem_insert Std.DHashMap.mem_insert_self
simp_lc whitelist Std.DHashMap.contains_insert Std.DHashMap.contains_insert_self
simp_lc whitelist Std.HashMap.contains_insert Std.HashMap.contains_insert_self

-- TODO: I'm similarly confused by these ones, which I can't seem to construct simp lemmas to resolve.
simp_lc whitelist Std.HashSet.insert_eq_insert LawfulSingleton.insert_emptyc_eq
simp_lc whitelist Std.HashMap.insert_eq_insert LawfulSingleton.insert_emptyc_eq
simp_lc whitelist Std.DHashMap.insert_eq_insert LawfulSingleton.insert_emptyc_eq

#guard_msgs (drop info) in
simp_lc check in Std Id LawfulSingleton _root_
