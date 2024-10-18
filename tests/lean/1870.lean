class One (α : Type u) where
  one : α

instance One.toOfNat1 {α} [One α] : OfNat α (nat_lit 1) where
  ofNat := ‹One α›.1

instance One.ofOfNat1 {α} [OfNat α (nat_lit 1)] : One α where
  one := 1

set_option pp.mvars false in
theorem ex1 : (@OfNat.ofNat Nat 0 Zero.toOfNat0) = @OfNat.ofNat Nat 1 One.toOfNat1 := by
  refine congrArg _ (congrArg _ ?_)
  rfl

example : (@OfNat.ofNat Nat 0 Zero.toOfNat0) = @OfNat.ofNat Nat 1 One.toOfNat1 := by
  apply congrArg
  apply congrArg
  apply rfl

theorem ex2 : (@OfNat.ofNat Nat 0 Zero.toOfNat0) = @OfNat.ofNat Nat 1 One.toOfNat1 := by
  apply congrArg
  apply congrArg
  apply rfl
