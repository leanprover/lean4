def f (x : Nat) : Nat :=
match x with
| 30  => 31
| y+1 => y
| 0   => 10

#eval f 20
#eval f 0
#eval f 30

universe u
infix:50 " ≅ " => HEq
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
by {
  subst h₁;
  assumption
}

theorem ex7 (a : Bool) (p q : Prop) (h₁ : a = true → p) (h₂ : a = false → q) : p ∨ q :=
  match (generalizing := false) h:a with
  | true  => Or.inl $ h₁ h
  | false => Or.inr $ h₂ h

theorem ex7' (a : Bool) (p q : Prop) (h₁ : a = true → p) (h₂ : a = false → q) : p ∨ q :=
  match a with
  | true  => Or.inl $ h₁ rfl
  | false => Or.inr $ h₂ rfl

def head {α} (xs : List α) (h : xs = [] → False) : α :=
  match he:xs with
  | []   => by contradiction
  | x::_ => x

variable {α : Type u} {p : α → Prop}

theorem ex8 {a1 a2 : {x // p x}} (h : a1.val = a2.val) : a1 = a2 :=
match a1, a2, h with
| ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

universe v
variable {β : α → Type v}

theorem ex9 {p₁ p₂ : Sigma (fun a => β a)} (h₁ : p₁.1 = p₂.1) (h : p₁.2 ≅ p₂.2) : p₁ = p₂ :=
match p₁, p₂, h₁, h with
| ⟨_, _⟩, ⟨_, _⟩, rfl, HEq.refl _ => rfl

inductive F : Nat → Type
| z : {n : Nat} → F (n+1)
| s : {n : Nat} → F n → F (n+1)

def f0 {α : Sort u} (x : F 0) : α :=
nomatch x

def f0' {α : Sort u} (x : F 0) : α :=
nomatch id x

def f1 {α : Sort u} (x : F 0 × Bool) : α :=
nomatch x

def f2 {α : Sort u} (x : Sum (F 0) (F 0)) : α :=
nomatch x

def f3 {α : Sort u} (x : Bool × F 0) : α :=
nomatch x

def f4 (x : Sum (F 0 × Bool) Nat) : Nat :=
match x with
| Sum.inr x => x

#eval f4 $ Sum.inr 100
