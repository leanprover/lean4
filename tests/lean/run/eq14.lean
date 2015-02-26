open nat decidable

definition has_decidable_eq : ∀ a b : nat, decidable (a = b)
| has_decidable_eq 0     0     := inl rfl
| has_decidable_eq (a+1) 0     := inr (λ h, nat.no_confusion h)
| has_decidable_eq 0     (b+1) := inr (λ h, nat.no_confusion h)
| has_decidable_eq (a+1) (b+1) :=
    if H : a = b
    then inl (eq.rec_on H rfl)
    else inr (λ h : a+1 = b+1, nat.no_confusion h (λ e : a = b, absurd e H))

check has_decidable_eq
print definition has_decidable_eq
