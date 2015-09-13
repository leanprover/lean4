import data.finset data.finset.card data.finset.equiv
open nat nat.finset decidable

namespace finset
variable {A : Type}
open finset (to_nat)
open finset (of_nat)

private lemma of_nat_eq_insert : ∀ {n s : nat}, n ∉ of_nat s → of_nat (2^n + s) = insert n (of_nat s)
| 0        s h := sorry
| (succ n) s h :=
  have n ∉ of_nat s,                     from sorry,
  assert of_nat s = insert n (of_nat s), from sorry,
  finset.ext (λ x,
  have gen : ∀ m, m ∈ of_nat (2^(succ n) + s) ↔ m ∈ insert (succ n) (of_nat s)
  | zero     :=
    assert aux₁ : odd (2^(succ n) + s) ↔ odd s, from sorry,
    calc
      0 ∈ of_nat (2^(succ n) + s) ↔ odd (2^(succ n) + s)           : sorry
                             ...  ↔ odd s                          : aux₁
                             ...  ↔ 0 ∈ insert (succ n) (of_nat s) : sorry
  | (succ m) := sorry,
  gen x)

end finset
