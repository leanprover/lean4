set_option pp.mvars false

/--
error: Type mismatch
  congrArg ?_ (congrArg ?_ ?_)
has type
  ?_ (?_ ?_) = ?_ (?_ ?_)
but is expected to have type
  OfNat.ofNat 0 = OfNat.ofNat 1
-/
#guard_msgs in
theorem ex1 : (@OfNat.ofNat Nat 0 Zero.toOfNat0) = @OfNat.ofNat Nat 1 One.toOfNat1 := by
  refine congrArg _ (congrArg _ ?_)
  rfl

/--
error: Tactic `apply` failed: could not unify the conclusion of `@congrArg`
  ?_ ?_ = ?_ ?_
with the goal
  OfNat.ofNat 0 = OfNat.ofNat 1

Note: The full type of `@congrArg` is
  ∀ {α : Sort _} {β : Sort _} {a₁ a₂ : α} (f : α → β), a₁ = a₂ → f a₁ = f a₂

⊢ OfNat.ofNat 0 = OfNat.ofNat 1
-/
#guard_msgs in
example : (@OfNat.ofNat Nat 0 Zero.toOfNat0) = @OfNat.ofNat Nat 1 One.toOfNat1 := by
  apply congrArg
  apply congrArg
  apply rfl

/--
error: Tactic `apply` failed: could not unify the conclusion of `@congrArg`
  ?_ ?_ = ?_ ?_
with the goal
  OfNat.ofNat 0 = OfNat.ofNat 1

Note: The full type of `@congrArg` is
  ∀ {α : Sort _} {β : Sort _} {a₁ a₂ : α} (f : α → β), a₁ = a₂ → f a₁ = f a₂

⊢ OfNat.ofNat 0 = OfNat.ofNat 1
-/
#guard_msgs in
theorem ex2 : (@OfNat.ofNat Nat 0 Zero.toOfNat0) = @OfNat.ofNat Nat 1 One.toOfNat1 := by
  apply congrArg
  apply congrArg
  apply rfl
