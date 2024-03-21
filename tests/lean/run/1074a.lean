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

/--
info: Brx.interp.eq_1 (n z : Term) (H_2 : Brx (Term.id2 n z)) :
  Brx.interp H_2 =
    match ⋯ with
    | ⋯ => Brx.interp Hz
-/
#guard_msgs in
#check Brx.interp.eq_1
