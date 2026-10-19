module

/-! The evaluator's independent challenge and approved proposition. -/

public section

@[expose] def Evaluator.approved : Prop := forall n : Nat, n + n = 2 * n
@[expose] def ClaimMeaning : Prop := False
@[expose] def Claim : Prop := ClaimMeaning
theorem success : True := by sorry
theorem protectedTarget : Claim := by sorry
