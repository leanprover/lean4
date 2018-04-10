open nat

def nat.ind_on {p : nat → Prop} (n : nat) (h₁ : p 0) (h₂ : ∀ n, p n → p (succ n)) : p n :=
nat.rec_on n h₁ h₂

example : ∀ a b : nat, a + b = b + a :=
begin
  intro a,
  apply nat.ind_on a,
  trace_state,
  repeat {admit}
end
