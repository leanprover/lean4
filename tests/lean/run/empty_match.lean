open nat

definition not_lt_zero (a : nat) : ¬ a < zero :=
assume H : a < zero,
match H with
end

check not_lt_zero
