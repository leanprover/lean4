import Lake.Build.Trace

/-! Sanity check for `Lake.Hash.ofHex`. -/

open Lake

#guard Hash.ofHex "0123456789" = ⟨0x0123456789⟩
#guard Hash.ofHex "abcdeF" = ⟨0xabcdef⟩
#guard Hash.ofHex "ABCDEF" = ⟨0xABCDEF⟩
