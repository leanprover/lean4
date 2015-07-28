import data.nat
open nat

example (a b c d : nat) : a + b = 0 → b = 0 → c + 1 + a = 1 → d = c - 1 → d = 0 :=
begin
  intro h₁ h₂,
  have aeq0 : a = 0, begin
    rewrite h₂ at h₁,
    exact h₁
  end,
  intro h₃ h₄,
  have deq0 : d = 0, begin
    have ceq : c = 0, begin
      rewrite aeq0 at h₃,
      rewrite add_zero at h₃,
      rewrite add_succ at h₃,
      rewrite add_zero at h₃,
      injection h₃, assumption
    end,
    rewrite ceq at h₄,
    repeat (esimp [sub, pred] at h₄),
    assumption
  end,
  exact deq0
end
