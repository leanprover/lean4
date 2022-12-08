infix:50 " ≅ "  => HEq
theorem ex1 {α : Sort u} {a b : α} (h : a ≅ b) : a = b :=
  match h with
  | HEq.refl _ => rfl

theorem ex2 {α : Sort u2} {a : α} {motive : {β : Sort u2} → β → Sort u1} (m : motive a) {β : Sort u2} {b : β} (h : a ≅ b) : motive b :=
  match h, m with
  | HEq.refl _, m => m

theorem ex3 {α : Sort u} {a : α} {p : α → Sort v} {b : α} (h₁ : a ≅ b) (h₂ : p a) : p b :=
  match h₁, h₂ with
  | HEq.refl _, h₂ => h₂

theorem ex4 {α β : Sort u} {a : α} {b : β} (h : a ≅ b) : b ≅ a :=
  match h with
  | HEq.refl _ => HEq.refl _

theorem ex5 {α : Sort u} {a a' : α} (h : a = a') : a ≅ a' :=
  match h with
  | rfl => HEq.refl _

theorem ex6 {α β : Sort u} (h : α = β) (a : α) : cast h a ≅ a :=
  match h with
  | rfl => HEq.refl _

theorem ex7 {α β σ : Sort u} {a : α} {b : β} {c : σ} (h₁ : a ≅ b) (h₂ : b ≅ c) : a ≅ c :=
  match h₁, h₂ with
  | HEq.refl _, HEq.refl _ => HEq.refl _
