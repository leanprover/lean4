module

public import Accepted

/-! A challenge statement whose meaning depends on another definition. -/

public section

def ClaimMeaning : Prop := False
def Claim : Prop := ClaimMeaning
theorem task : Claim := by sorry
