prelude
import init.meta init.logic init.data.nat.lemmas
import init.data.char.basic

namespace char
lemma of_nat_eq_of_lt {n : nat} : ∀ h : n < char_sz, of_nat n = fin.mk n h :=
begin
  intro h,
  unfold of_nat,
  cases (nat.decidable_lt n char_sz),
  {contradiction},
  {reflexivity}
end

lemma of_nat_eq_fin_of_ge {n : nat} : n ≥ char_sz → of_nat n = fin.mk 0 zero_lt_char_sz :=
begin
  intro h,
  unfold of_nat,
  cases (nat.decidable_lt n char_sz),
  {reflexivity},
  {note h' := not_lt_of_ge h, contradiction}
end

lemma of_nat_eq_of_ge {n : nat} : n ≥ char_sz → of_nat n = of_nat 0 :=
begin
  intro h,
  rw [of_nat_eq_fin_of_ge h]
end

lemma of_nat_ne_of_ne {n₁ n₂ : nat} (h₁ : n₁ ≠ n₂) (h₂ : n₁ < char_sz) (h₃ : n₂ < char_sz) : of_nat n₁ ≠ of_nat n₂ :=
begin
  rw [of_nat_eq_of_lt h₂, of_nat_eq_of_lt h₃],
  apply @fin.ne_of_vne _ (fin.mk n₁ h₂) (fin.mk n₂ h₃) h₁
end
end char
