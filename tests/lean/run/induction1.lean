@[recursor 4]
def Or.elim2 {p q r : Prop} (major : p ∨ q) (left : p → r) (right : q → r) : r :=
Or.elim major left right

new_frontend

theorem tst0 {p q : Prop } (h : p ∨ q) : q ∨ p :=
begin
  induction h;
  { apply Or.inr; assumption };
  { apply Or.inl; assumption }
end

theorem tst1 {p q : Prop } (h : p ∨ q) : q ∨ p :=
begin
  induction h with
  | inr h2 => exact Or.inl h2
  | inl h1 => exact Or.inr h1
end

theorem tst2 {p q : Prop } (h : p ∨ q) : q ∨ p :=
begin
  induction h using elim2 with
  | left _  => { apply Or.inr; assumption }
  | right _ => { apply Or.inl; assumption }
end

theorem tst3 {p q : Prop } (h : p ∨ q) : q ∨ p :=
begin
  induction h using elim2 with
  | right h => exact Or.inl h
  | left h  => exact Or.inr h
end

theorem tst4 {p q : Prop } (h : p ∨ q) : q ∨ p :=
begin
  induction h using elim2 with
  | right h => ?myright
  | left h  => ?myleft;
  case myleft  { exact Or.inr h };
  case myright { exact Or.inl h };
end

theorem tst5 {p q : Prop } (h : p ∨ q) : q ∨ p :=
begin
  induction h using elim2 with
  | right h => _
  | left h  => { refine Or.inr _; exact h };
  case right { exact Or.inl h }
end

theorem tst6 {p q : Prop } (h : p ∨ q) : q ∨ p :=
begin
  cases h with
  | inr h2 => exact Or.inl h2
  | inl h1 => exact Or.inr h1
end

theorem tst7 {α : Type} (xs : List α) (h : (a : α) → (as : List α) → xs ≠ a :: as) : xs = [] :=
begin
  induction xs with
  | nil          => exact rfl
  | cons z zs ih => exact absurd rfl (h z zs)
end

theorem tst8 {α : Type} (xs : List α) (h : (a : α) → (as : List α) → xs ≠ a :: as) : xs = [] :=
begin
  induction xs;
  exact rfl;
  exact absurd rfl $ h _ _
end

theorem tst9 {α : Type} (xs : List α) (h : (a : α) → (as : List α) → xs ≠ a :: as) : xs = [] :=
begin
  cases xs with
  | nil       => exact rfl
  | cons z zs => exact absurd rfl (h z zs)
end

theorem tst10 {p q : Prop } (h₁ : p ↔ q) (h₂ : p) : q :=
begin
  induction h₁ using Iff.elim with
  | _ h _ => exact h h₂
end

def Iff2 (m p q : Prop) := p ↔ q

theorem tst11 {p q r : Prop } (h₁ : Iff2 r p q) (h₂ : p) : q :=
begin
  induction h₁ using Iff.elim with
  | _ h _ => exact h h₂
end
