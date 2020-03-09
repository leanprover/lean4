universes u v

inductive Vec2 (α : Type u) (β : Type v) : Nat → Type (max u v)
| nil  : Vec2 0
| cons : α → β → forall {n}, Vec2 n → Vec2 (n+1)

new_frontend

theorem test1 {α β} {n} (a₁ a₂ : α) (b₁ b₂ : β) (v w : Vec2 α β n) (h : Vec2.cons a₁ b₁ v = Vec2.cons a₂ b₂ w) : a₁ = a₂ :=
begin
  injection h;
  assumption
end

theorem test2 {α β} {n} (a₁ a₂ : α) (b₁ b₂ : β) (v w : Vec2 α β n) (h : Vec2.cons a₁ b₁ v = Vec2.cons a₂ b₂ w) : v = w :=
begin
  injection h with h1 h2 h3 h4;
  assumption
end

theorem test3 {α β} {n} (a₁ a₂ : α) (b₁ b₂ : β) (v w : Vec2 α β n) (h : Vec2.cons a₁ b₁ v = Vec2.cons a₂ b₂ w) : v = w :=
begin
  injection h with _ _ _ h4;
  exact h4
end
