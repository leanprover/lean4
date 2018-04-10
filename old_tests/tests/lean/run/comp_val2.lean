open tactic

example : 'a' ≠ 'b' := by comp_val
example : '0' ≠ 'a' := by comp_val

example : "hello worlg" ≠ "hhello world" := by comp_val
example : "hello world" ≠ "hhello world" := by comp_val
example : "abc" ≠ "cde" := by comp_val
example : "abc" ≠ "" := by comp_val
example : "" ≠ "cde" := by comp_val

example : @fin.mk 5 3 dec_trivial ≠ @fin.mk 5 4 dec_trivial :=
by comp_val

example : @fin.mk 5 4 dec_trivial ≠ @fin.mk 5 1 dec_trivial :=
by comp_val
