class Zero'.{u} (α : Type u) where
  zero : α

instance Zero'.toOfNat0 {α} [Zero' α] : OfNat α (nat_lit 0) where
  ofNat := ‹Zero' α›.1

instance Nat.zero' : Zero' Nat where
  zero := 0

example :
    0 = if (b : Bool) then
      (@OfNat.ofNat.{0} Nat 0 (@Zero'.toOfNat0.{0} Nat (Nat.zero')))
    else
      Nat.zero := by
  simp
