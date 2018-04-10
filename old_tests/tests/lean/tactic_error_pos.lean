example (p q : Prop) (h1 : p) (h2 : q) : p ∧ q :=
begin
  exact (or.inl _)
       --^ type mismatch here (OK)
end

example (p q : Prop) (h1 : p) (h2 : q) : p ∧ q :=
begin
  exact (and.intro _ h2)
                 --^ don't know how to synthesize placeholder here (OK)
end

example (p q : Prop) (h1 : p) (h2 : q) : p ∧ q :=
begin
  abstract {exact (and.intro _ h2)}
                           --^ don't know how to synthesize placeholder here (OK)
end

example (p q : Prop) (h1 : p) (h2 : q) : p ∧ q :=
begin
  {exact (and.intro _ h2) } <|> apply and.intro
                  --^ should not show error here (BUG)
end

example (p q : Prop) (h1 : p) (h2 : q) : p ∧ q :=
begin
  try {exact (and.intro _ h2) }
                      --^ should not show error here (BUG)
end

example (p q : Prop) (h1 : p) (h2 : q) : p ∧ q :=
begin
  repeat {exact (and.intro _ h2) }
                         --^ should not show error here (BUG)
end

open tactic
meta def mytac : tactic unit :=
`[apply (or.inl _)]

example (p q : Prop) (h1 : p) (h2 : q) : p ∧ q :=
begin
  mytac
--^ failed to unify error here, it shoult *not* be at mytac or.inl (OK)
end
