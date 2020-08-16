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

theorem ex7 (a : Bool) (p q : Prop) (h₁ : a = true → p) (h₂ : a = false → q) : p ∨ q :=
match h:a with
| true  => Or.inl $ h₁ h
| false => Or.inr $ h₂ h

def head {α} (xs : List α) (h : xs = [] → False) : α :=
match he:xs with
| []   => False.elim $ h he
| x::_ => x

variables {α : Type u} {p : α → Prop}

theorem ex8 {a1 a2 : {x // p x}} (h : a1.val = a2.val) : a1 = a2 :=
match a1, a2, h with
| ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

universes v
variables {β : α → Type v}

theorem ex9 {p₁ p₂ : Sigma (fun a => β a)} (h₁ : p₁.1 = p₂.1) (h : p₁.2 ≅ p₂.2) : p₁ = p₂ :=
match p₁, p₂, h₁, h with
| ⟨_, _⟩, ⟨_, _⟩, rfl, HEq.refl _ => rfl

inductive F : Nat → Type
| z : {n : Nat} → F (n+1)
| s : {n : Nat} → F n → F (n+1)

def f0Elim {α : Sort u} (x : F 0) : α :=
nomatch x
