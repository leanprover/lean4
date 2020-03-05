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
  | inr h2 => Or.inl h2
  | inl h1 => Or.inr h1
end

theorem tst2 {p q : Prop } (h : p ∨ q) : q ∨ p :=
begin
  induction h using elim2 with
  | left _  => Or.inr $ by assumption
  | right _ => Or.inl $ by assumption
end

theorem tst3 {p q : Prop } (h : p ∨ q) : q ∨ p :=
begin
  induction h using elim2 with
  | right h => Or.inl h
  | left h  => Or.inr h
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
  | right h => Or.inl ?myright
  | left h  => Or.inr ?myleft;
  case myleft  assumption;
  case myright exact h;
end

theorem tst6 {p q : Prop } (h : p ∨ q) : q ∨ p :=
begin
  cases h with
  | inr h2 => Or.inl h2
  | inl h1 => Or.inr h1
end

theorem tst7 {α : Type} (xs : List α) (h : (a : α) → (as : List α) → xs ≠ a :: as) : xs = [] :=
begin
  induction xs with
  | nil          => rfl
  | cons z zs ih => absurd rfl (h z zs)
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
  | nil       => rfl
  | cons z zs => absurd rfl (h z zs)
end
