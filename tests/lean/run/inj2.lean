universe u v

inductive Vec2 (α : Type u) (β : Type v) : Nat → Type (max u v)
| nil  : Vec2 α β 0
| cons : α → β → forall {n}, Vec2 α β n → Vec2 α β (n+1)

inductive Fin2 : Nat → Type
| zero (n : Nat)              : Fin2 (n+1)
| succ {n : Nat} (s : Fin2 n) : Fin2 (n+1)

theorem test1 {α β} {n} (a₁ a₂ : α) (b₁ b₂ : β) (v w : Vec2 α β n) (h : Vec2.cons a₁ b₁ v = Vec2.cons a₂ b₂ w) : a₁ = a₂ :=
by {
  injection h;
  assumption
}

theorem test2 {α β} {n} (a₁ a₂ : α) (b₁ b₂ : β) (v w : Vec2 α β n) (h : Vec2.cons a₁ b₁ v = Vec2.cons a₂ b₂ w) : v = w :=
by {
  injection h with h1 h2 h3 h4;
  assumption
}

theorem test3 {α β} {n} (a₁ a₂ : α) (b₁ b₂ : β) (v w : Vec2 α β n) (h : Vec2.cons a₁ b₁ v = Vec2.cons a₂ b₂ w) : v = w :=
by {
  injection h with _ _ _ h4;
  exact h4
}

theorem test4 {α} (v : Fin2 0) : α :=
by cases v

def test5 {α β} {n} (v : Vec2 α β (n+1)) : α := by
  cases v with
  | cons h1 h2 n tail => exact h1

def test6 {α β} {n} (v : Vec2 α β (n+2)) : α := by
  cases v with
  | cons h1 h2 n tail => exact h1
