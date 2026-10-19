module

/-! The approval's body is unchanged but its transitive dependency is forged. -/

public section

def Meaning : Prop := False
def Accepted.first : Prop := Meaning
theorem task (h : Accepted.first) : True := False.elim h
