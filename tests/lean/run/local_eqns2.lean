import data.fin
open fin nat

definition nz_cases_on {C  : Π n, fin (succ n) → Type}
                       (H₁ : Π n, C n (fz n))
                       (H₂ : Π n (f : fin n), C n (fs f))
                       {n  : nat}
                       (f  : fin (succ n)) : C n f :=
begin
  reverts (n, f),
  show ∀ (n : nat) (f  : fin (succ n)), C n f
  |  m (fz m)  := by apply H₁
  |  m (fs f') := by apply H₂
end
