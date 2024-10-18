def UInt32.ofNatCore' (n : Nat) (h : n < UInt32.size) : UInt32 := {
  toBitVec := ⟨{ val := n, isLt := h }⟩
}

#eval UInt32.ofNatCore' 10 (by decide)

def UInt64.ofNatCore' (n : Nat) (h : n < UInt64.size) : UInt64 := {
  toBitVec := ⟨{ val := n, isLt := h }⟩
}

#eval UInt64.ofNatCore' 3 (by decide)

#eval toString $ { toBitVec := ⟨{ val := 3, isLt := (by decide) }⟩ : UInt8 }
#eval (3 : UInt8).val
#eval toString $ { toBitVec := ⟨{ val := 3, isLt := (by decide) }⟩ : UInt16 }
#eval (3 : UInt16).val
#eval toString $ { toBitVec := ⟨{ val := 3, isLt := (by decide) }⟩ : UInt32 }
#eval (3 : UInt32).val
#eval toString $ { toBitVec := ⟨{ val := 3, isLt := (by decide) }⟩ : UInt64 }
#eval (3 : UInt64).val
#eval toString $ { toBitVec := ⟨{ val := 3, isLt := (match System.Platform.numBits, System.Platform.numBits_eq with | _, Or.inl rfl => (by decide) | _, Or.inr rfl => (by decide)) }⟩ : USize }
#eval (3 : USize).val


#eval toString $ { toBitVec := ⟨{ val := 4, isLt := (by decide) }⟩ : UInt8 }
#eval (4 : UInt8).val
#eval toString $ { toBitVec := ⟨{ val := 4, isLt := (by decide) }⟩ : UInt16 }
#eval (4 : UInt16).val
#eval toString $ { toBitVec := ⟨{ val := 4, isLt := (by decide) }⟩ : UInt32 }
#eval (4 : UInt32).val
#eval toString $ { toBitVec := ⟨{ val := 4, isLt := (by decide) }⟩ : UInt64 }
#eval (4 : UInt64).val
#eval toString $ { toBitVec := ⟨{ val := 4, isLt := (match System.Platform.numBits, System.Platform.numBits_eq with | _, Or.inl rfl => (by decide) | _, Or.inr rfl => (by decide)) }⟩ : USize }
#eval (4 : USize).val
