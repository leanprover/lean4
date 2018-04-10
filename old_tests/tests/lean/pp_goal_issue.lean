constant f : (nat → nat → Prop) → Prop

example (h1 : false) : ∀ (a b c : nat), a = 0 → b = 0 → f (λ x y, a + x = b + c + y) :=
begin
  intros x x y h h, -- Force name clash
  trace_state,
  contradiction
end

example (h1 : false) : ∀ (a b c : nat), a = 0 → b = 0 → f (λ x y, a + x = b + c + y) :=
begin
  intros,
  trace_state,
  contradiction
end
