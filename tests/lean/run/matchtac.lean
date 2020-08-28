new_frontend

theorem tst1 {α : Type} {p : Prop} (xs : List α) (h₁ : (a : α) → (as : List α) → xs = a :: as → p) (h₂ : xs = [] → p) : p :=
begin
  match h:xs with
  | []    => exact h₂ h
  | z::zs => { apply h₁ z zs; assumption }
end

theorem tst2 {α : Type} {p : Prop} (xs : List α) (h₁ : (a : α) → (as : List α) → xs = a :: as → p) (h₂ : xs = [] → p) : p :=
begin
  match h:xs with
  | []    => ?nilCase
  | z::zs => ?consCase;
  case consCase exact h₁ z zs h;
  case nilCase exact h₂ h;
end

def tst3 {α β γ : Type} (h : α × β × γ) : β × α × γ :=
begin
  match h with
  | (a, b, c) => exact (b, a, c)
end
