inductive Term
| id2: Term -> Term -> Term

inductive Brx: Term -> Prop
| id2: Brx z -> Brx (Term.id2 n z)

def Brx.interp {a} (H: Brx a): Nat :=
  match a with
  | Term.id2 n z => by
    let ⟨Hn, Hz⟩: True ∧ Brx z
      := by cases H <;> exact ⟨by simp, by assumption⟩;
    exact Hz.interp

def Brx.interp_nil (H: Brx a): H.interp = H.interp
  :=
  by {
    unfold interp
    rfl
  }

#check Brx.interp._eq_1
