example (p q : Prop) : p ∧ q ↔ q ∧ p :=
begin
apply iff.intro,
  begin
     intro H,
     apply and.intro,
     apply (and.elim_right H),
     apply (and.elim_left H)
  end,
  begin
    intro H,
    apply and.intro,
    apply (and.elim_right H),
    apply (and.elim_left H)
  end
end

example (p q : Prop) : p ∧ q ↔ q ∧ p :=
begin
apply iff.intro,
  {intro H,
   apply and.intro,
   apply (and.elim_right H),
   apply (and.elim_left H)},
  {intro H,
   apply and.intro,
   apply (and.elim_right H),
   apply (and.elim_left H)}
end
