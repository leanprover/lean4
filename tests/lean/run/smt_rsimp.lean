constant p {α} : α → α → Prop
axiom pax {α} : ∀ n : α, p n n

open tactic

example (s t : list nat) (h : t = s) : p (s ++ []) ([] ++ t) :=
begin [smt]
  add_simp_lemmas,
  ematch,
  rsimp,
  guard_target p s s,
  apply pax
end
