namespace Ex1

variables
    (f : nat → nat → nat)
    (p : nat → nat → Prop)
    (h₁ : ∀ a b c, p b c → f a b = a)
    (x y z : nat)
    (h₂ : p y z)
include f h₁ x y z h₂
open tactic

example : f x y = 0 + x :=
begin
  rw [h₁],
  /- Resulting goals
     ... ⊢ x = 0 + x
     ... ⊢ p y ?m_1
     ... ⊢ ℕ  -- This is ?m_1
  -/
  (do n ← num_goals, guard $ n = 3),
  simp,
  exact h₂
end

example : f x y = 0 + x :=
begin
  rw [h₁] {new_goals := new_goals.non_dep_only},
  /- Resulting goals
     ... ⊢ x = 0 + x
     ... ⊢ p y ?m_1

     ?m_1 is not included as a new goal because it occurs above.
  -/
  (do n ← num_goals, guard $ n = 2),
  simp,
  exact h₂
end

example : f x y = 0 + x :=
begin
  rw [h₁] {new_goals := new_goals.all},
  /- Resulting goals
     ... ⊢ x = 0 + x
     ... ⊢ ℕ  -- This is ?m_1
     ... ⊢ p y ?m_1

     The order is preserved in this mode.
  -/
  (do n ← num_goals, guard $ n = 3),
  simp,
  exact z,
  exact h₂
end

end Ex1

namespace Ex2
open tactic

constant f : nat → nat
constant p : nat → Prop
/- The following lemma has an "auto_param", i.e., if `h` is not provided we
   try to synthesize it using the `assumption` tactic -/
lemma f_lemma (a : nat) (h : p a . assumption) : f a = a :=
sorry

/- `rw` has support for "auto_param"'s. -/
example (x : nat) (h : p x) : f x = 0 + x :=
begin
  rw [f_lemma],
  (do n ← num_goals, guard $ n = 1),
  simp
end

/- We can disable auto_param support. -/
example (x : nat) (h : p x) : f x = 0 + x :=
begin
  rw [f_lemma] {auto_param := ff},
  (do n ← num_goals, guard $ n = 2),
  simp,
  exact h
end

end Ex2
