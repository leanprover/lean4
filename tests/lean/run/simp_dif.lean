constant safe_div (a b : nat) : b ≠ 0 → nat

example (a b : nat) (h : ¬b ≠ 0) : (if h : b ≠ 0 then safe_div a b h else a) = a :=
by simp [dif_neg h]
example (a b : nat) (h : b ≠ 0) : (if h : b ≠ 0 then safe_div a b h else a) = safe_div a b h :=
by simp [dif_pos h]
example (a b : nat) (h : ¬b ≠ 0) : (if h : b ≠ 0 then safe_div a b h else a) = a :=
by rw [dif_neg h]
example (a b : nat) (h : b ≠ 0) : (if h : b ≠ 0 then safe_div a b h else a) = safe_div a b h :=
by rw [dif_pos h]

example (a b : nat) : (if h : b ≠ 0 then safe_div a b h else a) = a ∨ ∃ h, (if h : b ≠ 0 then safe_div a b h else a) = safe_div a b h :=
begin
  by_cases (b ≠ 0),
  {apply or.inr, rw [dif_pos h], existsi h, refl},
  {apply or.inl, rw [dif_neg h]}
end

example (a b : nat) : (if h : b ≠ 0 then safe_div a b h else a) = a ∨ ∃ h, (if h : b ≠ 0 then safe_div a b h else a) = safe_div a b h :=
begin
  by_cases (b ≠ 0),
  {apply or.inr, simp [dif_pos h], existsi h, trivial},
  {apply or.inl, simp [dif_neg h]}
end
