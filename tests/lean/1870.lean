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
