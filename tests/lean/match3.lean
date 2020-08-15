new_frontend

def f (x : Nat) : Nat :=
match x with
| 30  => 31
| y+1 => y
| 0   => 10

#eval f 20
#eval f 0
#eval f 30


universes u

theorem ex1 {α : Sort u} {a b : α} (h : a ≅ b) : a = b :=
match α, a, b, h with
| _, _, _, HEq.refl _ => rfl

theorem ex2 {α : Sort u} {a b : α} (h : a ≅ b) : a = b :=
match a, b, h with
| _, _, HEq.refl _ => rfl

theorem ex3 {α : Sort u} {a b : α} (h : a ≅ b) : a = b :=
match b, h with
| _, HEq.refl _ => rfl

theorem ex4  {α β : Sort u} {b : β} {a a' : α} (h₁ : a = a') (h₂ : a' ≅ b) : a ≅ b :=
match β, a', b, h₁, h₂ with
| _, _, _, rfl, HEq.refl _ => HEq.refl _

theorem ex5  {α β : Sort u} {b : β} {a a' : α} (h₁ : a = a') (h₂ : a' ≅ b) : a ≅ b :=
match a', h₁, h₂ with
| _, rfl, h₂ => h₂

theorem ex6  {α β : Sort u} {b : β} {a a' : α} (h₁ : a = a') (h₂ : a' ≅ b) : a ≅ b :=
begin
  subst h₁;
  assumption
end
