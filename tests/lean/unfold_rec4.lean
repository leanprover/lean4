open nat
definition f [unfold 1] (n : ℕ) : ℕ :=
by induction n with n fn; exact zero; exact succ (succ fn)

example (n : ℕ) : f (succ (succ n)) = sorry :=
begin
  unfold f,
end
