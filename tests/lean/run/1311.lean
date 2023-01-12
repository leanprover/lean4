instance : DecidableEq ByteArray
  | ⟨a⟩, ⟨b⟩ => {
      decide := decide (a = b)
      decide_iff := .trans decide_iff ⟨(· ▸ rfl), (by cases ·; rfl)⟩
    }

#eval ByteArray.empty = ByteArray.empty
#eval ByteArray.empty != ByteArray.empty.push 5

instance : BEq FloatArray where
  beq a b := match a, b with
    | ⟨a⟩, ⟨b⟩ => a == b

#eval FloatArray.empty == FloatArray.empty
#eval FloatArray.empty != FloatArray.empty.push 5
