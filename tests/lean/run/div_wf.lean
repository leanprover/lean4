open nat well_founded decidable prod

set_option pp.all true

-- Auxiliary lemma used to justify recursive call
private definition lt_aux {x y : nat} (H : 0 < y ∧ y ≤ x) : x - y < x :=
and.rec_on H (λ ypos ylex,
  sub_lt (nat.lt_of_lt_of_le ypos ylex) ypos)

definition wdiv.F (x : nat) (f : Π x₁, x₁ < x → nat → nat) (y : nat) : nat :=
if H : 0 < y ∧ y ≤ x then f (x - y) (lt_aux H) y + 1 else 0

definition wdiv (x y : nat) :=
fix lt_wf wdiv.F x y

theorem wdiv_def (x y : nat) : wdiv x y = if H : 0 < y ∧ y ≤ x then wdiv (x - y) y + 1 else 0 :=
congr_fun (well_founded.fix_eq lt_wf wdiv.F x) y

/-
See comment at fib_wrec.
example : wdiv 5 2 = 2 :=
rfl

example : wdiv 9 3 = 3 :=
rfl
-/

-- There is a little bit of cheating in the definition above.
-- I avoid the packing/unpacking into tuples.
-- The actual definitional package would not do that.
-- It will always pack things.

definition pair_nat.lt    := lex nat.lt nat.lt  -- Could also be (lex lt empty_rel)
definition pair_nat.lt.wf : well_founded pair_nat.lt :=
prod.lex_wf lt_wf lt_wf
infixl `≺`:50 := pair_nat.lt

-- Recursive lemma used to justify recursive call
definition plt_aux (x y : nat) (H : 0 < y ∧ y ≤ x) : (x - y, y) ≺ (x, y) :=
lex.left _ _ _ (lt_aux H)

definition pdiv.F (p₁ : nat × nat) : (Π p₂ : nat × nat, p₂ ≺ p₁ → nat) → nat :=
prod.cases_on p₁ (λ x y f,
  if H : 0 < y ∧ y ≤ x then f (x - y, y) (plt_aux x y H) + 1 else 0)

definition pdiv (x y : nat) :=
fix pair_nat.lt.wf pdiv.F (x, y)

theorem pdiv_def (x y : nat) : pdiv x y = if H : 0 < y ∧ y ≤ x then pdiv (x - y) y + 1 else 0 :=
well_founded.fix_eq pair_nat.lt.wf pdiv.F (x, y)

/-
See comment at fib_wrec.
example : pdiv 17 2 = 8 :=
rfl
-/
