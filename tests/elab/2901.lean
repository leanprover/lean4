def Vector' (α : Type u) (n : Nat) :=
  { l : List α // l.length = n }

inductive HVect : (n : Nat) -> (Vector' (Type v) n) -> Type (v+1)  where
   | Nil  : HVect 0 ⟨ [], simp ⟩
   | Cons : (t : Type v) -> (x : t) -> HVect n ⟨ts, p⟩ -> HVect (n+1) ⟨t::ts, by simp [p]⟩

def printHOK (v : HVect (n+1) ⟨String::ts, p'⟩) : String :=
   match v with
   | HVect.Cons _ x _ => (x : String)

def printHKO (v : HVect (n+1) ⟨String::ts, p'⟩) : String :=
   match v with
   | HVect.Cons _ x _ => "Hi"
