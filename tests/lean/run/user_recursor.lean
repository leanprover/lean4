import data.finset
check @and.rec

definition and.rec2 [recursor 4] {p r : Prop} (H₁ : p → r) (H₂ : p ∧ p) : r :=
and.rec_on H₂ (λ h₁ h₁, H₁ h₁)

set_option pp.all true
check ∃ x : nat, x = x

print [recursor] and.rec2
print [recursor] or.rec
print [recursor] and.rec
print [recursor] nat.rec
print [recursor] finset.induction
print [recursor] list.rec
print [recursor] Exists.rec
