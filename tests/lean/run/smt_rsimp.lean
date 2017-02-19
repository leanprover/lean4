constant p {α} : α → α → Prop
axiom pax {α} : ∀ n : α, p n n

open tactic

meta def check_expr (p : pexpr) (t : expr) : tactic unit :=
do e ← to_expr p, guard (t = e)

meta def check_target (p : pexpr) : tactic unit :=
target >>= check_expr p

example (s t : list nat) (h : t = s) : p (s ++ []) ([] ++ t) :=
begin [smt]
  add_simp_lemmas,
  ematch,
  rsimp,
  check_target `(p s s),
  apply pax
end
