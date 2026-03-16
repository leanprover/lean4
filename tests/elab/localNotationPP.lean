axiom n : Type → Type
section
local notation "ℕ" x => n x
end
#check n Nat -- should *not* be `ℕ Nat : Type`
