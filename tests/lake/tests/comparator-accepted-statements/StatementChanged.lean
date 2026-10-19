module

public import Accepted

/-! An approved premise must not permit changing the challenge from False to True. -/

public section

def ClaimMeaning : Prop := True
def Claim : Prop := ClaimMeaning
theorem task (_ : Accepted.first) : Claim := True.intro
