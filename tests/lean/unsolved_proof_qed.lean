example (a b c : nat) (H₁ : a = b) (H₂ : b = c) : a = c :=
proof eq.trans H₁ _ qed

example (a b c : nat) (H₁ : a = b) (H₂ : b = c) : a = c :=
have aux : c = a, proof eq.trans _ (eq.symm H₁) qed,
(eq.symm aux)
