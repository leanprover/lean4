instance : DecidableEq ByteArray
  | ⟨a⟩, ⟨b⟩ => match decEq a b with
    | isTrue h₁  => isTrue $ congrArg ByteArray.mk h₁
    | isFalse h₂ => isFalse $ fun h => by cases h; cases (h₂ rfl)

/-- info: true -/
#guard_msgs in
#eval ByteArray.empty = ByteArray.empty

/-- info: true -/
#guard_msgs in
#eval ByteArray.empty != ByteArray.empty.push 5

instance : BEq FloatArray where
  beq a b := match a, b with
    | ⟨a⟩, ⟨b⟩ => a == b

/-- info: true -/
#guard_msgs in
#eval FloatArray.empty == FloatArray.empty

/-- info: true -/
#guard_msgs in
#eval FloatArray.empty != FloatArray.empty.push 5
