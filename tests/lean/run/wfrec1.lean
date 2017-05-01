private definition S := Σ a : nat, nat
private definition R : S → S → Prop := sigma.skip_left nat (<)
private definition Rwf : well_founded R :=
  sigma.skip_left_wf nat nat.lt_wf
private definition f_aux : ∀ (p₁ : S), (∀ p₂ : S, R p₂ p₁ → nat) → nat
| (sigma.mk n (m+1)) F := F (sigma.mk (n+10) (m - n)) (sigma.mk_skip_left _ _ (nat.sub_lt_succ _ _))
| (sigma.mk n 0)     F := n

definition f (n m : nat) : nat :=
well_founded.fix Rwf f_aux (sigma.mk n m)

lemma f.eq_1 (n m : nat) : f n (m+1) = f (n+10) (m - n) :=
well_founded.fix_eq Rwf f_aux (sigma.mk n (m+1))

lemma f.eq_2 (n m : nat) : f n 0 = n :=
well_founded.fix_eq Rwf f_aux (sigma.mk n 0)
