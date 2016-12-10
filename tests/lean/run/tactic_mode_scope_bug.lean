example (p q : Prop) : p ∧ q → q ∧ p :=
begin
  intro h,
  have hp : p, from h^.left,
  have hq : q, from h^.right,
  ⟨hq, hp⟩
end

example (p q : Prop) (hp : q) (hq : p) : p ∧ q → q ∧ p :=
begin
  intro h,
  have hp : p, from h^.left,
  have hq : q, from h^.right,
  ⟨hq, hp⟩
end
