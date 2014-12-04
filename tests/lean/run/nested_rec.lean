open nat prod sigma

-- We will define the following example by well-foudned recursion
--   g 0        := 0
--   g (succ x) := g (g x)
definition g.F (x : nat) : (Π y, y < x → Σ r : nat, r ≤ y) → Σ r : nat, r ≤ x :=
nat.cases_on x
  (λ f, (dpair zero (le.refl zero)))
  (λ x₁ (f : Π y, y < succ x₁ → Σ r : nat, r ≤ y),
     let p₁    := f x₁ (lt.base x₁) in
     let gx₁   := dpr₁ p₁ in
     let p₂    := f gx₁ (lt.of_le_of_lt (dpr₂ p₁) (lt.base x₁)) in
     let ggx₁  := dpr₁ p₂ in
     dpair ggx₁ (le.step (le.trans (dpr₂ p₂) (dpr₂ p₁))))

definition g (x : nat) : nat :=
dpr₁ (well_founded.fix g.F x)

example : g 3 = 0 :=
rfl

example : g 6 = 0 :=
rfl

theorem g_zero : g 0 = 0 :=
rfl

theorem g_succ (a : nat) : g (succ a) = g (g a) :=
have aux : well_founded.fix g.F (succ a) = dpair (g (g a)) _, from
  well_founded.fix_eq g.F (succ a),
calc g (succ a) = dpr₁ (well_founded.fix g.F (succ a)) : rfl
          ...   = dpr₁ (dpair (g (g a)) _)             : aux
          ...   = g (g a)                              : rfl

theorem g_all_zero (a : nat) : g a = zero :=
nat.induction_on a
  g_zero
  (λ a₁ (ih : g a₁ = zero), calc
     g (succ a₁) = g (g a₁) : g_succ
          ...    = g 0      : ih
          ...    = 0        : g_zero)
