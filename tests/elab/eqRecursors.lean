def castRec {α : Type u} {m n : Nat} (h : m = n) (v : Vector α m) : Vector α n := Eq.rec v h
def castNdrec {α : Type u} {m n : Nat} (h : m = n) (v : Vector α m) : Vector α n := Eq.ndrec v h
def castRecOn {α : Type u} {m n : Nat} (h : m = n) (v : Vector α m) : Vector α n := Eq.recOn h v
def castCasesOn {α : Type u} {m n : Nat} (h : m = n) (v : Vector α m) : Vector α n := Eq.casesOn h v
