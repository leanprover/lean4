import tools.super
open tactic

constant nat_has_dvd : has_dvd nat
attribute [instance] nat_has_dvd

noncomputable def prime (n : ℕ) := ∀d, d ∣ n → d = 1 ∨ d = n
axiom dvd_refl (m : ℕ) : m ∣ m
axiom dvd_mul (m n k : ℕ) : m ∣ n → m ∣ (n*k)

axiom nat_mul_cancel_one (m n : ℕ) : m = m * n → n = 1

example {m n : ℕ} : prime (m * n) → m = 1 ∨ n = 1 :=
by super with dvd_refl dvd_mul nat_mul_cancel_one

example : nat.zero ≠ nat.succ nat.zero := by super
example (x y : ℕ) : nat.succ x = nat.succ y → x = y := by super
example (i) (a b c : i) : [a,b,c] = [b,c,a] -> a = b ∧ b = c := by super

definition is_positive (n : ℕ) := n > 0
example (n : ℕ) : n > 0 ↔ is_positive n := by super

example (m n : ℕ) : 0 + m = 0 + n → m = n :=
by super with nat.zero_add

example : ∀x y : ℕ, x + y = y + x :=
begin intros, induction x, note h : nat.zero = 0 := rfl,
      super with nat.add_zero nat.zero_add,
      super with nat.add_succ nat.succ_add end

example (i) [inhabited i] : nonempty i := by super
example (i) [nonempty i] : ¬(inhabited i → false) := by super

example : nonempty ℕ := by super
example : ¬(inhabited ℕ → false) := by super

example {a b} : ¬(b ∨ ¬a) ∨ (a → b) := by super
example {a} : a ∨ ¬a := by super
example {a} : (a ∧ a) ∨ (¬a ∧ ¬a) := by super
example (i) (c : i) (p : i → Prop) (f : i → i) :
  p c → (∀x, p x → p (f x)) → p (f (f (f c))) := by super

example (i) (p : i → Prop) : ∀x, p x → ∃x, p x := by super

example (i) [nonempty i] (p : i → i → Prop) : (∀x y, p x y) → ∃x, ∀z, p x z := by super

example (i) [nonempty i] (p : i → Prop) : (∀x, p x) → ¬¬∀x, p x := by super

-- Requires non-empty domain.
example {i} [nonempty i] (p : i → Prop) :
  (∀x y, p x ∨ p y) → ∃x y, p x ∧ p y := by super

example (i) (a b : i) (p : i → Prop) (H : a = b) : p b → p a :=
by super

example (i) (a b : i) (p : i → Prop) (H : a = b) : p a → p b :=
by super

example (i) (a b : i) (p : i → Prop) (H : a = b) : p b = p a :=
by super

example (i) (c : i) (p : i → Prop) (f g : i → i) :
p c → (∀x, p x → p (f x)) → (∀x, p x → f x = g x) → f (f c) = g (g c) :=
by super

example (i) (p q : i → i → Prop) (a b c d : i) :
  (∀x y z, p x y ∧ p y z → p x z) →
  (∀x y z, q x y ∧ q y z → q x z) →
  (∀x y, q x y → q y x) →
  (∀x y, p x y ∨ q x y) →
  p a b ∨ q c d :=
by super

-- This example from Davis-Putnam actually requires a non-empty domain

example (i) [nonempty i] (f g : i → i → Prop) :
  ∃x y, ∀z, (f x y → f y z ∧ f z z) ∧ (f x y ∧ g x y → g x z ∧ g z z) :=
by super

example (person) [nonempty person] (drinks : person → Prop) :
  ∃canary, drinks canary → ∀other, drinks other := by super

example {p q : ℕ → Prop} {r} : (∀x y, p x ∧ q y ∧ r) -> ∀x, (p x ∧ r ∧ q x) := by super
