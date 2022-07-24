instance : DecidableEq ByteArray
  | ⟨a⟩, ⟨b⟩ => match decEq a b with
    | isTrue h₁  => isTrue $ congrArg ByteArray.mk h₁
    | isFalse h₂ => isFalse $ fun h => by cases h; cases (h₂ rfl)

#eval ByteArray.empty = ByteArray.empty
#eval ByteArray.empty != ByteArray.empty.push 5
