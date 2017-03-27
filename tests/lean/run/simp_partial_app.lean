open tactic

example (a : list nat) : a = [1, 2] → a^.for nat.succ = [2, 3] :=
begin
  intros,
  simp [list.for, flip],
  guard_target list.map nat.succ a = [2, 3],
  subst a,
  simp [list.map]
end

constant f {α : Type} [has_zero α] (a b : α) : a ≠ 0 → b ≠ 0 → α
axiom fax {α : Type} [has_zero α] (a : α) : f a = λ b h₁ h₂, a

lemma ex : f 1 2 dec_trivial dec_trivial = 1 :=
begin
  simp [fax]
end
