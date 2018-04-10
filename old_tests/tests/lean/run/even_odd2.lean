mutual def even, odd
with even : nat → bool
| 0     := tt
| (a+1) := odd a
with odd : nat → bool
| 0     := ff
| (a+1) := even a
using_well_founded {rel_tac := λ f eqns, tactic.trace f >> tactic.trace eqns >> tactic.apply_instance}

example (a : nat) : even (a + 1) = odd a :=
by simp [even]

example (a : nat) : odd (a + 1) = even a :=
by simp [odd]

lemma even_eq_not_odd : ∀ a, even a = bnot (odd a) :=
begin
  intro a, induction a,
  simp [even, odd],
  simp [*, even, odd]
end
