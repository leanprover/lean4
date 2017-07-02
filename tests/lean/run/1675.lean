def foo (a b : nat) : Prop :=
a = 0 ∧ b = 0

attribute [simp] foo

example (p : nat → Prop) (a b : nat) : foo a b → p (a + b) → p 0 :=
begin
  intros h₁ h₂,
  simp_all
end

example (a b : nat) (p : nat → Prop) (h₁ : a = b + 0) (h₂ : b = 0) (h₃ : p a) : p 0 ∧ a = 0 :=
by simp_all

constant q : Prop
axiom q_lemma : q

open tactic
example (a b : nat) (p : nat → Prop) (h₁ : a = b + 0) (h₂ : b = 0) (h₃ : p a) : p 0 ∧ a = 0 ∧ q :=
begin
  simp_all,
  guard_target q,
  do {e₁ ← get_local `h₁ >>= infer_type, e₂ ← to_expr ```(a = 0), guard (e₁ = e₂)},
  do {e₁ ← get_local `h₃ >>= infer_type, e₂ ← to_expr ```(p 0), guard (e₁ = e₂)},
  apply q_lemma
end

example (p : nat → Prop) (a b : nat) : a = 0 ∧ b = 0 → p (a + b) → p 0 :=
begin
  intros h₁ h₂,
  simp [h₁] at *,
  assumption
end

example (p : Prop) : p :=
begin
  fail_if_success {simp_all}, -- simp_all should fail if nothing was simplified
  simp_all {fail_if_unchanged := ff}, -- should work
  admit
end

example (p : Prop) : let h : 0 = 0 := rfl in p :=
begin
  intro h,
  simp_all,
  do {e₁ ← get_local `h >>= infer_type, e₂ ← to_expr ```(true), guard (e₁ = e₂)},
  admit
end
