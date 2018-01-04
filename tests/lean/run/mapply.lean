constant p : nat → Prop
constant q : nat → Prop
constant h : nat → Prop
axiom pq0 : q 0 → p 0
axiom phx : ∀ x, h x → p x

example (h₁ : h 1) : ∃ x, p x :=
begin
  constructor,
  mapply pq0 <|> mapply phx, -- The first `mapply` should fail
  assumption
end

open nat
example : ∃ x, succ 0 > x :=
begin
  constructor,
  fail_if_success { mapply succ_lt_succ },
  apply zero_lt_succ
end
