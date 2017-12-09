structure S (f : nat → nat) :=
(ax : ∀ x, f x = x . tactic.assumption)

example (g : nat → nat) (s : S g) (x : nat) : g (g x) = x :=
by simp [s.ax]
