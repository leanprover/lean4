open nat
definition seq_diagram (A : ℕ → Type) : Type := (Πn, A n → A (succ n))
variables (A : ℕ → Type) (f : seq_diagram A)
include f

definition shift_diag [unfold_full] (k : ℕ) : seq_diagram (λn, A (k + n)) :=
λn a, f (k + n) a

example (n k : ℕ) (b : A (k + n)) : shift_diag A f k n b = sorry :=
begin
  esimp,
  state,
  apply sorry
end
