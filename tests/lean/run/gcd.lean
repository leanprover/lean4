open nat well_founded decidable prod

namespace playground

-- Setup
definition pair_nat.lt    := lex nat.lt nat.lt
definition pair_nat.lt.wf : well_founded pair_nat.lt :=
prod.lex_wf lt_wf lt_wf
infixl `≺`:50 := pair_nat.lt

-- Lemma for justifying recursive call
private lemma lt₁ (x₁ y₁ : nat) : (x₁ - y₁, succ y₁) ≺ (succ x₁, succ y₁) :=
lex.left _ _ _ (lt_succ_of_le (sub_le x₁ y₁))

-- Lemma for justifying recursive call
private lemma lt₂ (x₁ y₁ : nat) : (succ x₁, y₁ - x₁) ≺ (succ x₁, succ y₁) :=
lex.right _ _ (lt_succ_of_le (sub_le y₁ x₁))

definition gcd.F (p₁ : nat × nat) : (Π p₂ : nat × nat, p₂ ≺ p₁ → nat) → nat :=
prod.cases_on p₁ (λ (x y : nat),
nat.cases_on x
  (λ f, y) -- x = 0
  (λ x₁, nat.cases_on y
     (λ f, succ x₁) -- y = 0
     (λ y₁ (f : (Π p₂ : nat × nat, p₂ ≺ (succ x₁, succ y₁) → nat)),
        if y₁ ≤ x₁ then f (x₁ - y₁, succ y₁) (lt₁ _ _ )
                   else f (succ x₁, y₁ - x₁) (lt₂ _ _))))

definition gcd (x y : nat) :=
fix pair_nat.lt.wf gcd.F (x, y)

theorem gcd_def_z_y (y : nat) : gcd 0 y = y :=
well_founded.fix_eq pair_nat.lt.wf gcd.F (0, y)

theorem gcd_def_sx_z (x : nat) : gcd (x+1) 0 = x+1 :=
well_founded.fix_eq pair_nat.lt.wf gcd.F (x+1, 0)

theorem gcd_def_sx_sy (x y : nat) : gcd (x+1) (y+1) = if y ≤ x then gcd (x-y) (y+1) else gcd (x+1) (y-x) :=
well_founded.fix_eq pair_nat.lt.wf gcd.F (x+1, y+1)

end playground
