open nat

definition not_lt_zero (a : nat) : ¬ a < 0 :=
assume H : a < 0,
match H with
end

#check _root_.not_lt_zero
