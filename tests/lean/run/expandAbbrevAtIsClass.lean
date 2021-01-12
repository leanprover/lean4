def one (α : Type u) [OfNat α (natLit! 1)] : α := 1

abbrev HasOne (α : Type u) := OfNat α (natLit! 1)

def one' (α : Type u) [HasOne α] : α := 1

example : HasOne Nat := inferInstance
