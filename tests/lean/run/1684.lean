set_option trace.compiler.result true

def Iff.elim1.{u} {a b : Prop} {motive : Sort u} (t : a ↔ b) (h : (mp : a → b) → (mpr : b → a) → motive) : motive :=
  match t with | ⟨hab, hba⟩ => h hab hba

def Iff.elim2.{u} {a b : Prop} {motive : Sort u} (t : a ↔ b) (h : (mp : a → b) → (mpr : b → a) → motive) : motive :=
  Iff.casesOn (motive:= fun _ : a ↔ b => motive) t h
