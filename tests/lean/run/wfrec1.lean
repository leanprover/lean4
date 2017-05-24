private def S := psigma (λ _ : nat, nat)
private def R : S → S → Prop := psigma.skip_left nat (<)
private def Rwf : well_founded R :=
  psigma.skip_left_wf nat nat.lt_wf

private def f_aux : ∀ (p₁ : S), (∀ p₂ : S, R p₂ p₁ → nat) → nat
| ⟨n, m+1⟩ F := F ⟨n+10, m - n⟩ (psigma.mk_skip_left _ _ (nat.sub_lt_succ _ _))
| ⟨n, 0⟩   F := n

def f (n m : nat) : nat :=
well_founded.fix Rwf f_aux ⟨n, m⟩

lemma f.eq_1 (n m : nat) : f n (m+1) = f (n+10) (m - n) :=
well_founded.fix_eq Rwf f_aux ⟨n, m+1⟩

lemma f.eq_2 (n m : nat) : f n 0 = n :=
well_founded.fix_eq Rwf f_aux ⟨n, 0⟩
