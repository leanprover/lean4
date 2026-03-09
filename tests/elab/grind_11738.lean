/--
error: `grind` failed
case grind
k : Rat
hk : 2 ≤ k
h : ¬0 ≤ k
⊢ False
-/
#guard_msgs in
example (k : Rat) (hk : 2 ≤ k) : 0 ≤ k := by lia -verbose -- Should fail

example (k : Rat) (hk : 2 ≤ k) : 0 ≤ k := by grind
