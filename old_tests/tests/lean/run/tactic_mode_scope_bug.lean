example (p q : Prop) : p ∧ q → q ∧ p :=
begin
  intro h,
  have hp : p := h^.left,
  have hq : q := h^.right,
  exact ⟨hq, hp⟩
end

example (p q : Prop) (hp : q) (hq : p) : p ∧ q → q ∧ p :=
begin
  intro h,
  have hp : p := h^.left,
  have hq : q := h^.right,
  exact ⟨hq, hp⟩
end
