/-!
# Examples from documentation added in https://github.com/leanprover/lean4/pull/4166
-/

#guard "abc".prev ⟨2⟩ = String.Pos.mk 1
#guard "abc".prev ⟨0⟩ = String.Pos.mk 0
#guard "L∃∀N".prev ⟨4⟩ = String.Pos.mk 1
#guard "abc".front = 'a'
#guard "".front = (default : Char)
#guard "abc".back = 'c'
#guard "".back = (default : Char)
#guard "abc".atEnd ⟨2⟩ = false
#guard "abc".atEnd ⟨3⟩ = true
#guard "L∃∀N".atEnd ⟨8⟩ = true
