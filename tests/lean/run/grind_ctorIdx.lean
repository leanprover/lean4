
inductive T where
| con1 : Nat → T
| con2 : T

opaque double (n : Nat) : T := .con2


example (heq_1 : double n = .con1 5) : (double n).ctorIdx = 0 := by
  grind

example  (h : (double n).ctorIdx > 5) (heq_1 : double n = .con1 5) : False := by
  grind

example  (h : Nat.hasNotBit 1 0) : False := by
  grind

example  (h : Nat.hasNotBit 1 (double n).ctorIdx) (heq_1 : double n = .con1 5) : False := by
  grind

inductive IT : Nat → Type where
| con1 n : IT n
| con2 : IT 0

example (heq_1 : (x : IT m) ≍ (IT.con1 4)) : x.ctorIdx = 0 := by
  fail_if_success grind
  sorry

example (hm : m = 4) (heq_1 : (x : IT m) ≍ (IT.con1 4)) : x.ctorIdx = 0 := by
  -- Can we make this work?
  fail_if_success grind
  subst m
  grind
