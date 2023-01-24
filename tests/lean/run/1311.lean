instance : DecidableEq ByteArray :=
  .ofInj (fun ⟨a⟩ => a) @fun ⟨a⟩ ⟨b⟩ h => by simp_all

#eval ByteArray.empty = ByteArray.empty
#eval ByteArray.empty != ByteArray.empty.push 5

instance : BEq FloatArray where
  beq a b := match a, b with
    | ⟨a⟩, ⟨b⟩ => a == b

#eval FloatArray.empty == FloatArray.empty
#eval FloatArray.empty != FloatArray.empty.push 5
