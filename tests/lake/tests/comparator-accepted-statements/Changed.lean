module

/-! Same-named approved propositions with different meanings must be rejected. -/

public section

def Accepted.first : Prop := False
def Accepted.second : Prop := forall n : Nat, n + 0 = n
def Accepted.unused : Prop := True
theorem task (h : Accepted.first) : True := False.elim h
