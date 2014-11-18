import data.nat data.prod
open nat well_founded decidable prod eq.ops

-- I use "dependent" if-then-else to be able to communicate the if-then-else condition
-- to the branches
definition dite (c : Prop) [H : decidable c] {A : Type} (t : c → A) (e : ¬ c → A) : A :=
decidable.rec_on H (assume Hc, t Hc) (assume Hnc, e Hnc)

notation `dif` c `then` t:45 `else` e:45 := dite c t e

-- Auxiliary lemma used to justify recursive call
private lemma lt_aux {x y : nat} (H : 0 < y ∧ y ≤ x) : x - y < x :=
have y0 : 0 < y, from and.elim_left H,
have x0 : 0 < x, from lt_le_trans y0 (and.elim_right H),
sub_lt x0 y0

definition wdiv.F (x : nat) (f : Π x₁, x₁ < x → nat → nat) (y : nat) : nat :=
dif 0 < y ∧ y ≤ x then (λ Hp, f (x - y) (lt_aux Hp) y + 1) else (λ Hn, zero)

definition wdiv (x y : nat) :=
fix wdiv.F x y

eval wdiv 6 2

theorem wdiv_def (x y : nat) : wdiv x y = if 0 < y ∧ y ≤ x then wdiv (x - y) y + 1 else 0 :=
congr_fun (well_founded.fix_eq wdiv.F x) y

-- There is a little bit of cheating in the definition above.
-- I avoid the packing/unpacking into tuples.
-- The actual definitional package would not do that.
-- It will always pack things.

definition pair_nat.lt    := lex lt lt  -- Could also be (lex lt empty_rel)
definition pair_nat.lt.wf [instance] : well_founded pair_nat.lt := prod.lex.wf lt.wf lt.wf
infixl `≺`:50 := pair_nat.lt

-- Recursive lemma used to justify recursive call
private lemma plt_aux (p : nat × nat) (H : 0 < pr₂ p ∧ pr₂ p ≤ pr₁ p) : (pr₁ p - pr₂ p, pr₂ p) ≺ p :=
have aux₁ : pr₁ p - pr₂ p < pr₁ p, from lt_aux H,
have aux₂ : (pr₁ p - pr₂ p, pr₂ p) ≺ (pr₁ p, pr₂ p), from !lex.left aux₁,
prod.eta p ▸ aux₂

definition pdiv.F (p₁ : nat × nat) (f : Π p₂ : nat × nat, p₂ ≺ p₁ → nat) : nat :=
let x := pr₁ p₁ in
let y := pr₂ p₁ in
dif 0 < y ∧ y ≤ x then (λ Hp, f (x - y, y) (plt_aux p₁ Hp) + 1) else (λ Hnp, zero)

definition pdiv (x y : nat) :=
fix pdiv.F (x, y)

eval pdiv 9 2

theorem pdiv_def (x y : nat) : pdiv x y = if 0 < y ∧ y ≤ x then pdiv (x - y) y + 1 else zero :=
well_founded.fix_eq pdiv.F (x, y)

-- Remark: dite and ite are "definitionally equal" when we ignore the proofs.
-- I used that, when I wrote div_def and pdiv_def.
theorem dite_ite_eq (c : Prop) [H : decidable c] {A : Type} (t : A) (e : A) :
      dite c (λ Hc, t) (λ Hnc, e) = ite c t e :=
rfl
