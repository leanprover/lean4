inductive Term : Type
| id: Term -> Term

inductive Brx: Term -> Prop
| id: Brx z -> Brx (Term.id n)

def Brx.interp {a} (H: Brx a): Nat :=
  match a with
  | Term.id n => by
    have ⟨Hn, Hz⟩: True ∧ Brx z
      := by cases H <;> exact ⟨by simp, by assumption⟩;
    exact Hz.interp
