import standard
namespace int

private lemma sub_nat_nat_elim (m n : ℕ) (P : ℕ → ℕ → ℤ → Prop)
  (hp : ∀i n, P (n + i) n (of_nat i))
  (hn : ∀i m, P m (m + i + 1) (-[1+ i])) :
  P m n (sub_nat_nat m n) :=
sorry

inductive rel_int_nat_nat : ℤ → ℕ × ℕ → Prop
| pos : ∀m p, rel_int_nat_nat (of_nat p) (m + p, m)
| neg : ∀m n, rel_int_nat_nat (neg_succ_of_nat n) (m, m + n)

lemma rel_sub_nat_nat {a b : ℕ} : rel_int_nat_nat (sub_nat_nat a b) (a, b) :=
/- The next statement kills lean  -/
sub_nat_nat_elim a b (λ(a b : ℕ) (i : ℤ), rel_int_nat_nat i (a, b)) sorry sorry

end int
