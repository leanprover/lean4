import data.num data.bool

open bool well_founded

namespace pos_num

definition lt_pred (a b : pos_num) : Prop := lt a b = tt

definition not_lt_one1 (a : pos_num) : ¬ lt_pred a one :=
begin
  esimp [lt_pred],
  intro H,
  apply (absurd_of_eq_ff_of_eq_tt (lt_one_right_eq_ff a) H)
end

open tactic well_founded

print raw intro -- intro is overloaded

definition not_lt_one2 (a : pos_num) : ¬ lt_pred a one :=
begin
  esimp [lt_pred],
  intro H,
  apply (absurd_of_eq_ff_of_eq_tt (lt_one_right_eq_ff a) H)
end

end pos_num
