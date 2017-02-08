open tactic expr

meta definition is_op_app (op : expr) (e : expr) : option (expr × expr) :=
match e with
| (app (app fn a1) a2) := if op = fn then some (a1, a2) else none
| e                    := none
end

meta definition flat_with : expr → expr → expr → expr → tactic (expr × expr)
| op assoc e rhs :=
  match (is_op_app op e) with
  | (some (a1, a2)) :=  do
    -- H₁ is a proof for a2 + rhs = rhs₁
    (rhs₁, H₁)     ← flat_with op assoc a2 rhs,
    -- H₂ is a proof for a1 + rhs₁ = rhs₂
    (new_app, H₂)  ← flat_with op assoc a1 rhs₁,
    -- We need to generate a proof that (a1 + a2) + rhs = a1 + (a2 + rhs)
    -- H₃ is a proof for (a1 + a2) + rhs = a1 + (a2 + rhs)
    H₃             ← return $ assoc a1 a2 rhs,
    -- H₃ is a proof for a1 + (a2 + rhs) = a1 + rhs1
    H₄             ← to_expr `(congr_arg %%(app op a1) %%H₁),
    H₅             ← to_expr `(eq.trans %%H₃ %%H₄),
    H              ← to_expr `(eq.trans %%H₅ %%H₂),
    return (new_app, H)
  | none          := do
    new_app ← return $ op e rhs,
    H       ← to_expr `(eq.refl %%new_app),
    return (new_app, H)
  end

meta definition flat : expr → expr → expr → tactic (expr × expr)
| op assoc e :=
  match (is_op_app op e) with
  | (some (a1, a2)) := do
    -- H₁ is a proof that a2 = new_a2
    (new_a2, H₁)   ← flat op assoc a2,
    -- H₂ is a proof that a1 + new_a2 = new_app
    (new_app, H₂)  ← flat_with op assoc a1 new_a2,
    -- We need a proof that (a1 + a2) = new_app
    -- H₃ is a proof for a1 + a2 = a1 + new_a2
    H₃ : expr      ← to_expr `(congr_arg %%(app op a1) %%H₁),
    H              ← to_expr `(eq.trans %%H₃ %%H₂),
    return (new_app, H)
  | none          :=
    do pr ← to_expr `(eq.refl %%e),
       return (e, pr)
  end

local infix `+` := nat.add
set_option trace.app_builder true
set_option pp.all true

example (a b c d e f g : nat) : ((a + b) + c) + ((d + e) + (f + g))  = a + (b + (c + (d + (e + (f + g))))) :=
by do
  assoc : expr ← mk_const `nat.add_assoc,
  op : expr    ← mk_const `nat.add,
  tgt          ← target,
  match is_eq tgt with
  | (some (lhs, rhs)) := do
    r ← flat op assoc lhs,
    exact r.2
  | none            := failed
  end
