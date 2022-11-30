class Zero.{u} (α : Type u) where
  zero : α

instance Zero.toOfNat0 {α} [Zero α] : OfNat α (nat_lit 0) where
  ofNat := ‹Zero α›.1

instance Zero.ofOfNat0 {α} [OfNat α (nat_lit 0)] : Zero α where
  zero := 0

class One (α : Type u) where
  one : α

instance One.toOfNat1 {α} [One α] : OfNat α (nat_lit 1) where
  ofNat := ‹One α›.1

instance One.ofOfNat1 {α} [OfNat α (nat_lit 1)] : One α where
  one := 1

theorem ex1 : (@OfNat.ofNat Nat 0 Zero.toOfNat0) = @OfNat.ofNat Nat 1 One.toOfNat1 := by
  refine' congr_arg _ (congr_arg _ _)
  rfl

example : (@OfNat.ofNat Nat 0 Zero.toOfNat0) = @OfNat.ofNat Nat 1 One.toOfNat1 := by
  apply congr_arg
  apply congr_arg
  apply rfl

theorem ex2 : (@OfNat.ofNat Nat 0 Zero.toOfNat0) = @OfNat.ofNat Nat 1 One.toOfNat1 := by
  apply congr_arg
  apply congr_arg
  apply rfl
