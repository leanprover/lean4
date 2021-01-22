variable {α : Type _} (r : α → α → Prop) (π : α → α)

inductive rel : α → α → Prop
| of {x y} : r x y → rel x y
| compat {x y} : rel x y → rel (π x) (π y)
| refl (x) : rel x x
| symm {x y} : rel x y → rel y x
| trans {x y z} : rel x y → rel y z → rel x z

def thing : Setoid α := ⟨rel r π, ⟨rel.refl, rel.symm, rel.trans⟩⟩

def β := Quotient (thing r π)

variable {γ : Type _}

def Quotient.mk' {s : Setoid α} (a : α) : Quotient s :=
Quotient.mk a

def Quotient.sound' {s : Setoid α} {a b : α} (h : a ≈ b) : Quotient.mk a = Quotient.mk b :=
Quotient.sound h

def δ0 : β r π → β r π :=
Quotient.lift
  (s := thing r π)
  (Quotient.mk' $ π ·)
  fun x y h => Quotient.sound' (by exact rel.compat h)

def δ1 : β r π → β r π :=
Quotient.lift
  (s := thing r π)
  (Quotient.mk' $ π ·)
  fun x y h => Quotient.sound' (rel.compat h)

def δ2 : β r π → β r π :=
Quotient.lift
  (s := thing r π)
  (Quotient.mk' $ π ·)
  (by exact fun x y h => Quotient.sound' (rel.compat h))

def Quotient.lift' {α β} {s : Setoid α} (f : α → β) (h : (a b : α) → a ≈ b → f a = f b) (q : Quotient s) : β :=
Quotient.lift f h q

def δ3 : β r π → β r π :=
Quotient.lift'
  (Quotient.mk' $ π ·)
  fun x y h => Quotient.sound' (rel.compat h)

def δ4 : β r π → β r π :=
@Quotient.lift _ _
  (thing r π)
  (Quotient.mk' $ π ·)
  (fun x y h => Quotient.sound' (rel.compat h))

def δ5 : β r π → β r π :=
@Quotient.lift' _ _ _
  (Quotient.mk' $ π ·)
  (fun x y h => Quotient.sound' (rel.compat h))
