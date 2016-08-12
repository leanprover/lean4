constant Sum : (nat → nat) → nat → nat

attribute [forward]
lemma l1 (f : nat → nat) : Sum f 0 = 0 :=
sorry

print l1
