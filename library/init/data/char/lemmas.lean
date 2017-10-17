prelude
import init.meta init.logic init.data.nat.lemmas
import init.data.char.basic

namespace char
lemma val_of_nat_eq_of_is_valid {n : nat} : is_valid_char n → (of_nat n).val = n :=
by intro h; unfold of_nat; rw [dif_pos h]

lemma val_of_nat_eq_of_not_is_valid {n : nat} : ¬ is_valid_char n → (of_nat n).val = 0 :=
by intro h; unfold of_nat; rw [dif_neg h]

lemma of_nat_eq_of_not_is_valid {n : nat} : ¬ is_valid_char n → of_nat n = of_nat 0 :=
by intro h; apply eq_of_veq; rw [val_of_nat_eq_of_not_is_valid h]; reflexivity

lemma of_nat_ne_of_ne {n₁ n₂ : nat} (h₁ : n₁ ≠ n₂) (h₂ : is_valid_char n₁) (h₃ : is_valid_char n₂) : of_nat n₁ ≠ of_nat n₂ :=
begin
  apply ne_of_vne,
  rw [val_of_nat_eq_of_is_valid h₂, val_of_nat_eq_of_is_valid h₃],
  assumption
end
end char
