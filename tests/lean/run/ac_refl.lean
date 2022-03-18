open Lean

instance : IsAssociative (α := Nat) HAdd.hAdd := ⟨Nat.add_assoc⟩
instance : IsCommutative (α := Nat) HAdd.hAdd := ⟨Nat.add_comm⟩
instance : IsNeutral HAdd.hAdd 0 := ⟨Nat.zero_add, Nat.add_zero⟩

instance : IsAssociative (α := Nat) HMul.hMul := ⟨Nat.mul_assoc⟩
instance : IsCommutative (α := Nat) HMul.hMul := ⟨Nat.mul_comm⟩
instance : IsNeutral HMul.hMul 1 := ⟨Nat.one_mul, Nat.mul_one⟩

theorem max_assoc (n m k : Nat) : max (max n m) k = max n (max m k) := by
  simp [max]; split <;> split <;> try split <;> try rfl
  case inl hmn nhkn hkm => exact False.elim $ nhkn $ Nat.lt_trans hkm hmn
  . rfl
  case inl nhmn nhkm hkn => apply absurd hkn; simp [Nat.not_lt_eq] at *; exact Nat.le_trans nhmn nhkm

theorem max_comm (n m : Nat) : max n m = max m n := by
  simp [max]; split <;> split <;> try rfl
  case inl h₁ h₂ => apply absurd (Nat.lt_trans h₁ h₂); apply Nat.lt_irrefl
  case inr h₁ h₂ => simp [Nat.not_lt_eq] at *; apply Nat.le_antisymm <;> assumption

theorem max_idem (n : Nat) : max n n = n := by
  simp [max]

theorem Nat.zero_max (n : Nat) : max 0 n = n := by
  simp [max]; rfl

theorem Nat.max_zero (n : Nat) : max n 0 = n := by
  rw [max_comm, Nat.zero_max]

instance : IsAssociative (α := Nat) max := ⟨max_assoc⟩
instance : IsCommutative (α := Nat) max := ⟨max_comm⟩
instance : IsIdempotent (α := Nat) max := ⟨max_idem⟩
instance : IsNeutral max 0 := ⟨Nat.zero_max, Nat.max_zero⟩

instance : IsAssociative And := ⟨λ p q r => propext ⟨λ ⟨⟨hp, hq⟩, hr⟩ => ⟨hp, hq, hr⟩, λ ⟨hp, hq, hr⟩ => ⟨⟨hp, hq⟩, hr⟩⟩⟩
instance : IsCommutative And := ⟨λ p q => propext ⟨λ ⟨hp, hq⟩ => ⟨hq, hp⟩, λ ⟨hq, hp⟩ => ⟨hp, hq⟩⟩⟩
instance : IsIdempotent And := ⟨λ p => propext ⟨λ ⟨hp, _⟩ => hp, λ hp => ⟨hp, hp⟩⟩⟩
instance : IsNeutral And True :=
  ⟨λ p => propext ⟨λ ⟨_, hp⟩ => hp, λ hp => ⟨True.intro, hp⟩⟩, λ p => propext ⟨λ ⟨hp, _⟩ => hp, λ hp => ⟨hp, True.intro⟩⟩⟩

theorem or_assoc (p q r : Prop) : ((p ∨ q) ∨ r) = (p ∨ q ∨ r) :=
  propext ⟨λ hpqr => hpqr.elim (λ hpq => hpq.elim Or.inl $ λ hq => Or.inr $ Or.inl hq) $ λ hr => Or.inr $ Or.inr hr,
    λ hpqr => hpqr.elim (λ hp => Or.inl $ Or.inl hp) $ λ hqr => hqr.elim (λ hq => Or.inl $ Or.inr hq) Or.inr⟩

instance : IsAssociative Or := ⟨or_assoc⟩
instance : IsCommutative Or := ⟨λ p q => propext ⟨λ hpq => hpq.elim Or.inr Or.inl, λ hqp => hqp.elim Or.inr Or.inl⟩⟩
instance : IsIdempotent Or := ⟨λ p => propext ⟨λ hp => hp.elim id id, Or.inl⟩⟩
instance : IsNeutral Or False :=
  ⟨λ p => propext ⟨λ hfp => hfp.elim False.elim id, Or.inr⟩, λ p => propext ⟨λ hpf => hpf.elim id False.elim, Or.inl⟩⟩

example (x y z : Nat) : x + y + 0 + z = z + (x + y) := by ac_refl

example (x y z : Nat) : (x + y) * (0 + z) = (x + y) * z:= by ac_refl

example (x y z : Nat) : (x + y) * (0 + z) = 1 * z * (y + 0 + x) := by ac_refl

theorem ex₁ (x y z : Nat) : max (0 + (max x (max z (max (0 + 0) ((max 1 0) + 0 + 0) * y)))) y = max (max x y) z := by ac_refl
#print ex₁

example (x y : Nat) : 1 + 0 + 0 = 0 + 1 := by ac_refl

example (x y : Nat) : (x + y = 42) = (y + x = 42) := by ac_refl

example (x y : Nat) (P : Prop) : (x + y = 42 → P) = (y + x = 42 → P) := by ac_refl

inductive Vector (α : Type u) : Nat → Type u where
  | nil  : Vector α 0
  | cons : α → Vector α n → Vector α (n+1)

def f (n : Nat) (xs : Vector α n) := xs

-- Repro: Dependent types trigger incorrect proofs
theorem ex₂ (n m : Nat) (xs : Vector α (n+m)) (ys : Vector α (m+n)) : (f (n+m) xs, f (m+n) ys, n+m) = (f (n+m) xs, f (m+n) ys, m+n) := by
  ac_refl

-- Repro: Binders also trigger invalid proofs
theorem ex₃ (n : Nat) : (fun x => n + x) = (fun x => x + n) := by
  ac_refl
#print ex₃

-- Repro: the Prop universe doesn't work
example (p q : Prop) : (p ∨ p ∨ q ∧ True) = (q ∨ p) := by
  ac_refl
