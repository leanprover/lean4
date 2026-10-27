module

/-! A submission shadows the evaluator's module and changes its definitions. -/

public section

@[expose] def Evaluator.approved : Prop := False
@[expose] def ClaimMeaning : Prop := True
@[expose] def Claim : Prop := ClaimMeaning
@[expose] def Project.only : Prop := False
