open tactic

example : (1:int) ≠ 2 :=
by comp_val

example : (1:int) ≠ 0 :=
by comp_val

example : (0:int) ≠ 1 :=
by comp_val

example : (3:int) ≠ 0 :=
by comp_val

example : (2:int) ≠ 1 :=
by comp_val

example : (3:int) ≠ -4 :=
by comp_val

example : (3:int) ≠ 4 :=
by comp_val

example : (100:int) ≠ 42919 :=
by comp_val

example : 42919 ≠ (100:int) :=
by comp_val

example : -(3:int) ≠ 49391 :=
by comp_val

example : -(3:int) ≠ 3 :=
by comp_val

example : -(100:int) ≠ -42919 :=
by comp_val

example : 0 ≠ -(1:int) :=
by comp_val

example : 0 ≠ -(100:int) :=
by comp_val

example : 0 ≠ -(2:int) :=
by comp_val

example : -(23:int) ≠ 0 :=
by comp_val

example : -(1 : int) ≠ 0 :=
by comp_val
