set_option pp.mvars false

/--
error: type mismatch
  congrArg ?_ (congrArg ?_ ?_)
has type
  ?_ (?_ ?_) = ?_ (?_ ?_) : Prop
but is expected to have type
  OfNat.ofNat 0 = OfNat.ofNat 1 : Prop
-/
#guard_msgs in
theorem ex1 : (@OfNat.ofNat Nat 0 Zero.toOfNat0) = @OfNat.ofNat Nat 1 One.toOfNat1 := by
  refine congrArg _ (congrArg _ ?_)
  rfl

/--
error: tactic 'apply' failed, failed to unify
  ?_ ?_ = ?_ ?_
with
  OfNat.ofNat 0 = OfNat.ofNat 1
⊢ OfNat.ofNat 0 = OfNat.ofNat 1
-/
#guard_msgs in
example : (@OfNat.ofNat Nat 0 Zero.toOfNat0) = @OfNat.ofNat Nat 1 One.toOfNat1 := by
  apply congrArg
  apply congrArg
  apply rfl

/--
error: tactic 'apply' failed, failed to unify
  ?_ ?_ = ?_ ?_
with
  OfNat.ofNat 0 = OfNat.ofNat 1
⊢ OfNat.ofNat 0 = OfNat.ofNat 1
-/
#guard_msgs in
theorem ex2 : (@OfNat.ofNat Nat 0 Zero.toOfNat0) = @OfNat.ofNat Nat 1 One.toOfNat1 := by
  apply congrArg
  apply congrArg
  apply rfl
