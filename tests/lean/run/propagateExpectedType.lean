variable {α : Type _} (r : α → α → Prop) (π : α → α)

inductive Rel : α → α → Prop
| of {x y} : r x y → Rel x y
| compat {x y} : Rel x y → Rel (π x) (π y)
| refl (x) : Rel x x
| symm {x y} : Rel x y → Rel y x
| trans {x y z} : Rel x y → Rel y z → Rel x z

def thing : Setoid α := ⟨Rel r π, ⟨Rel.refl, Rel.symm, Rel.trans⟩⟩

def β := Quotient (thing r π)

variable {γ : Type _}

abbrev Quotient.mk'' {s : Setoid α} (a : α) : Quotient s :=
Quotient.mk s a

def δ0 : β r π → β r π :=
Quotient.lift
  (s := thing r π)
  (Quotient.mk'' $ π ·)
  fun x y h => Quotient.sound (by exact Rel.compat h)

def δ1 : β r π → β r π :=
Quotient.lift
  (s := thing r π)
  (Quotient.mk'' $ π ·)
  fun x y h => Quotient.sound (Rel.compat h)

def δ2 : β r π → β r π :=
Quotient.lift
  (s := thing r π)
  (Quotient.mk'' $ π ·)
  (by exact fun x y h => Quotient.sound (Rel.compat h))

def Quotient.lift' {α β} {s : Setoid α} (f : α → β) (h : (a b : α) → a ≈ b → f a = f b) (q : Quotient s) : β :=
Quotient.lift f h q

def δ3 : β r π → β r π :=
Quotient.lift'
  (Quotient.mk'' $ π ·)
  fun x y h => Quotient.sound (Rel.compat h)

def δ4 : β r π → β r π :=
@Quotient.lift _ _
  (thing r π)
  (Quotient.mk'' $ π ·)
  (fun x y h => Quotient.sound (Rel.compat h))

def δ5 : β r π → β r π :=
@Quotient.lift' _ _ _
  (Quotient.mk'' $ π ·)
  (fun x y h => Quotient.sound (Rel.compat h))
