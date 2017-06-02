lemma ex3 (a b c : nat) : a + 0 = 0 + a ∧ b = b :=
begin
  constructor ; [skip, skip, skip]
            --^ The "insufficient number of goals" error message should be reported here.
end

lemma ex4 (a b c : nat) : a + 0 = 0 + a ∧ b = b :=
begin
  constructor; [skip, skip, skip]
--^ Flycheck reports the error here if the `;` occurs immediately after the first tactic.
-- This is not ideal, but this is a flycheck issue. Ther error is reported in the right place by Lean.
end

lemma ex5 (a : nat) : a = a ∧ a = a :=
begin
  constructor ; [refl]
            --^ "insufficient number of tactics" error
end

lemma ex6 (a : nat) : a = a ∧ a = a :=
begin
  constructor ; []
            --^ "insufficient number of tactics" error
end

lemma ex7 (a : nat) : a = a ∧ a = a :=
begin
  constructor ; [refl, refl]
end
