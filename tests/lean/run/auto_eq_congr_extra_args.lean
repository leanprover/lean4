open tactic

constant my_ite (c : Prop) {A : Type*} (t : A) : A
@[simp] lemma my_ite_true {A : Type*} (t : A) : @my_ite true A t = t := sorry

def my_true_def : Prop := true
@[simp] lemma m_true_def_true : my_true_def = true := rfl

constant my_true : Prop
@[simp] lemma m_true_true : my_true = true := sorry

example (n : ℕ) (f : ℕ → ℕ) : my_ite true f n = f n := by simp
example (n : ℕ) (f g : ℕ → ℕ) : my_ite my_true f n = f n := by simp
example (n : ℕ) (f g : ℕ → ℕ) : my_ite my_true_def f n = f n := by simp
example (A : Type) (a : A) (f : Π (A : Type), A → A) : my_ite true f A a = f A a := by simp

@[congr] lemma my_ite_congr {A : Type*} (c₁ c₂ : Prop) (t₁ t₂ : A) :
  (c₁ ↔ c₂) → (t₁ = t₂) → my_ite c₁ t₁ = my_ite c₂ t₂ := sorry

example (n : ℕ) (f : ℕ → ℕ) : my_ite true f n = f n := by simp
example (n : ℕ) (f g : ℕ → ℕ) : my_ite my_true f n = f n := by simp
example (n : ℕ) (f g : ℕ → ℕ) : my_ite my_true_def f n = f n := by simp
example (A : Type) (a : A) (f : Π (A : Type), A → A) : my_ite my_true f A a = f A a := by simp
