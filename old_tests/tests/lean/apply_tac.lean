example (a b c : nat) (h₁ : a = b) (h₂ : b = c) : a = c :=
begin
  apply eq.trans _ h₂,
  -- the metavars created during elaboration become new goals
  trace_state,
  exact h₁
end

example (a : nat) : ∃ x, x = a :=
begin
  apply exists.intro,
  -- the goal for the witness should occur "after" the goal for x = a
  trace_state,
  refl
end

example (a : nat) : ∃ x, x = a :=
begin
  eapply exists.intro,
  -- only metavars with out forward dependencies are added as goals.
  trace_state,
  refl
end

example (a : nat) : ∃ x, x = a :=
begin
  fapply exists.intro,
  -- all unassigned metavars are added as new goals using the order they were created.
  trace_state,
  exact a,
  trace_state,
  refl
end

example {α : Type} [partial_order α] (a : α) : a = a :=
begin
  apply le_antisymm,
  apply le_refl,
  apply le_refl
end

def f (a := 10) : ℕ := a + 1

def bla : nat :=
begin
  apply f -- uses opt_param for solving goal
end

example : bla = 11 :=
rfl

open tactic

lemma foo {a b c : nat} (h₁ : a = b) (h₂ : b = c . assumption) : a = c :=
eq.trans h₁ h₂

example (a b c : nat) (h₁ : a = b) (h₂ : b = c) : a = c :=
begin
  apply @foo a b c h₁ -- uses auto_param for solving goal
end

lemma my_div_self (a : nat) (h : a ≠ 0 . assumption) : a / a = 1 :=
sorry

example (a : nat) (h : a ≠ 0) : a / a = 1 :=
begin
  apply my_div_self -- uses auto_param for solving goal
end

example (a b c : nat) (h₁ : a = b) (h₂ : b = c) : a = c :=
begin
  apply_with (@foo a b c h₁) {auto_param := ff},
  assumption
end

example (a : nat) (h : a ≠ 0) : a / a = 1 :=
begin
  apply_with my_div_self {auto_param := ff},
  assumption
end

example (a : nat) (h : a ≠ 0) : a / a = 1 :=
begin
  apply_with my_div_self {opt_param := ff} -- uses auto_param for solving goal
end

def bla2 : nat :=
begin
  apply_with f {opt_param := ff},
  exact 20
end

example : bla2 = 21 :=
rfl
