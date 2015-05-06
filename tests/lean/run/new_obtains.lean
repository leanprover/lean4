import data.nat

theorem tst2 (A B C D : Type) : (A × B) × (C × D) → C × B × A :=
assume p : (A × B) × (C × D),
obtain [a b] [c d], from p,
(c, b, a)

theorem tst (a b c d : Prop) : (a ∧ b) ∧ (c ∧ d) → c ∧ b ∧ a :=
assume H,
obtain [Ha Hb] Hc Hd, from H,
and.intro Hc (and.intro Hb Ha)

theorem tst22 (A B C D : Type) : (A × B) × (C × D) → C × B × A :=
assume p,
obtain [a b] [c d], from p,
(c, b, a)

theorem tst3 (A B C D : Type) : A × B × C × D → C × B × A :=
assume p,
obtain [[a b] c] d, from p,
(c, b, a)

example (p : nat → nat → Prop) : (∃ x, p x x) → ∃ x y, p x y :=
assume ex,
obtain x pxx, from ex,
exists.intro x (exists.intro x pxx)

example (p q : nat → nat → Prop) : (∃ x y, p x y ∧ q x y ∧ q y x) → ∃ x y, p x y :=
assume ex,
obtain x y pxy qxy qyx, from ex,
exists.intro x (exists.intro y pxy)

example (p : nat → nat → Type): (Σ x, p x x) → (Σ x y, p x y) :=
assume sig,
obtain x pxx, from sig,
⟨x, x, pxx⟩

example (p q : nat → nat → Type) : (Σ x y, p x y × q x y × q y x) → Σ x y, p x y :=
assume ex : Σ x y, p x y × q x y × q y x,
obtain x y [[pxy qxy] qyx], from ex,
⟨x, y, pxy⟩

example (p q : nat → nat → Type) : (Σ x y, p x y × q x y × q y x) → Σ x y, p x y :=
assume ex,
have ex1 : Σ x y, p x y × q x y × q y x, from ex,
obtain x y [[pxy qxy] qyx], from ex1,
⟨x, y, pxy⟩

example (p q : nat → nat → Type) : (Σ x y, p x y × q x y × q y x) → Σ x y, p x y :=
assume ex,
obtain x y [[pxy qxy] qyx], from ex,
⟨x, y, pxy⟩

open nat

definition even (a : nat) := ∃ x, a = 2*x

example (a b : nat) (H₁ : even a) (H₂ : even b) : even (a+b) :=
obtain x (Hx : a = 2*x), from H₁,
obtain y (Hy : b = 2*y), from H₂,
exists.intro
  (x+y)
  (calc a+b = 2*x + 2*y : by rewrite [Hx, Hy]
        ... = 2*(x+y)   : by rewrite mul.left_distrib)

theorem dvd_of_dvd_add_left {m n₁ n₂ : ℕ} (H₁ : m ∣ n₁ + n₂) (H₂ : m ∣ n₁) : m ∣ n₂ :=
obtain (c₁ : nat) (Hc₁ : n₁ + n₂ = m * c₁), from H₁,
obtain (c₂ : nat) (Hc₂ : n₁ = m * c₂), from H₂,
have   aux : m * (c₁ - c₂) = n₂, from calc
  m * (c₁ - c₂) = m * c₁  - m * c₂ : by rewrite mul_sub_left_distrib
           ...  = n₁ + n₂ - m * c₂ : Hc₁
           ...  = n₁ + n₂ - n₁     : Hc₂
           ...  = n₂               : add_sub_cancel_left,
dvd.intro aux
