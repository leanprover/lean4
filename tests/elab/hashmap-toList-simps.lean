import Std.Data.DHashMap.Lemmas
import Std.Data.HashMap.Lemmas

section
variable [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Std.HashMap α β} {k : α} {v : β}

#check_simp (k, v) ∈ m.toList ~> m.getKey? k = some k ∧ m[k]? = some v

end

section
variable [BEq α] [Hashable α] [LawfulBEq α] {m : Std.HashMap α β} {k : α} {v : β}

#check_simp (k, v) ∈ m.toList ~> m[k]? = some v

end

section
variable [BEq α] [Hashable α] [LawfulBEq α] {m : Std.DHashMap α β} {k : α} {v : β k}

#check_simp ⟨k, v⟩ ∈ m.toList ~> m.get? k = some v

end
