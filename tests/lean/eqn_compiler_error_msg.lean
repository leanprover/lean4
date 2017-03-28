inductive R : ℕ → Prop
| pos : ∀p n, R (p + n)

lemma R_id : ∀n, R n → R n
| (.(p) + .(n)) (R.pos p n) := R.pos p n
