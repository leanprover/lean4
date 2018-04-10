structure S (f : nat → nat) :=
(ax : ∀ x, f x = x . tactic.assumption)

example (g : nat → nat) (s : S g) (x : nat) : g (g x) = x :=
by simp [s.ax]

constant h : nat → nat
axiom h_ax (x : nat) (p : x > 0 . tactic.comp_val) : h x = x

example (a : nat) : a > 0 → h a = a :=
begin
  intros, simp [h_ax, *]
end
