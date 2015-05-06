open prod sigma

theorem tst2 (A B C D : Type) : (A × B) × (C × D) → C × B × A :=
assume p : (A × B) × (C × D),
obtain [a b] [c d], from p,
(c, (b, a))

theorem tst22 (A B C D : Type) : (A × B) × (C × D) → C × B × A :=
assume p,
obtain [a b] [c d], from p,
(c, (b, a))

theorem tst3 (A B C D : Type) : A × B × C × D → C × B × A :=
assume p,
obtain a b c d, from p,
(c, (b, a))

example (p q : nat → nat → Type) : (Σ x y, p x y × q x y × q y x) → Σ x y, p x y :=
assume ex,
obtain x y pxy qxy qyx, from ex,
⟨x, y, pxy⟩

example (p : nat → nat → Type): (Σ x, p x x) → (Σ x y, p x y) :=
assume sig,
obtain x pxx, from sig,
⟨x, x, pxx⟩

open nat
definition even (a : nat) := Σ x, a = 2*x

example (a b : nat) (H₁ : even a) (H₂ : even b) : even (a+b) :=
obtain x (Hx : a = 2*x), from H₁,
obtain y (Hy : b = 2*y), from H₂,
⟨x+y,
 calc a+b = 2*x + 2*y : by rewrite [Hx, Hy]
      ... = 2*(x+y)   : sorry⟩
