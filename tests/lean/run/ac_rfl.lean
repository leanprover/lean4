open Std

instance : Associative (α := Nat) HAdd.hAdd := ⟨Nat.add_assoc⟩
instance : Commutative (α := Nat) HAdd.hAdd := ⟨Nat.add_comm⟩
instance : LawfulCommIdentity HAdd.hAdd 0 where right_id := Nat.add_zero

instance : Associative (α := Nat) HMul.hMul := ⟨Nat.mul_assoc⟩
instance : Commutative (α := Nat) HMul.hMul := ⟨Nat.mul_comm⟩
instance : LawfulCommIdentity HMul.hMul 1 where right_id := Nat.mul_one

@[simp] theorem succ_le_succ_iff {x y : Nat} : x.succ ≤ y.succ ↔ x ≤ y :=
  ⟨Nat.le_of_succ_le_succ, Nat.succ_le_succ⟩

@[simp] theorem add_le_add_right_iff {x y z : Nat} : x + z ≤ y + z ↔ x ≤ y := by
  induction z <;> simp_all [Nat.add_succ]

set_option linter.unusedVariables false in
theorem le_ext : ∀ {x y : Nat} (h : ∀ z, z ≤ x ↔ z ≤ y), x = y
  | 0, 0, _ => rfl
  | x+1, y+1, h => congrArg (· + 1) <| le_ext fun z => have := h (z + 1); by simp_all
  | 0, y+1, h => have := h 1; by clear h; simp_all
  | x+1, 0, h => have := h 1; by simp_all

theorem le_or_le : ∀ (a b : Nat), a ≤ b ∨ b ≤ a
  | x+1, y+1 => by simp [le_or_le x y]
  | 0, 0 | x+1, 0 | 0, y+1 => by simp

theorem le_of_not_le {a b : Nat} (h : ¬ a ≤ b) : b ≤ a :=
  match le_or_le a b with | .inl ab => (h ab).rec | .inr ba => ba

@[simp] theorem le_max_iff {x y z : Nat} : x ≤ max y z ↔ x ≤ y ∨ x ≤ z := by
  simp only [Nat.max_def]
  split
  · exact Iff.intro .inr fun | .inl xy => Nat.le_trans ‹_› ‹_› | .inr xz => ‹_›
  · exact Iff.intro .inl fun | .inl xy => ‹_› | .inr xz => Nat.le_trans ‹_› (le_of_not_le ‹_›)

theorem max_assoc (n m k : Nat) : max (max n m) k = max n (max m k) :=
  le_ext (by simp [or_assoc])

theorem max_comm (n m : Nat) : max n m = max m n :=
  le_ext (by simp [or_comm])

theorem max_idem (n : Nat) : max n n = n := le_ext (by simp)

theorem Nat.zero_max (n : Nat) : max 0 n = n := by simp [Nat.max_def]

theorem Nat.max_zero (n : Nat) : max n 0 = n := by rw [max_comm, Nat.zero_max]

instance : Associative (α := Nat) max := ⟨max_assoc⟩
instance : Commutative (α := Nat) max := ⟨max_comm⟩
instance : IdempotentOp (α := Nat) max := ⟨max_idem⟩
instance : LawfulCommIdentity max 0 where
  right_id := Nat.max_zero

instance : Associative And := ⟨λ _p _q _r => propext ⟨λ ⟨⟨hp, hq⟩, hr⟩ => ⟨hp, hq, hr⟩, λ ⟨hp, hq, hr⟩ => ⟨⟨hp, hq⟩, hr⟩⟩⟩
instance : Commutative And := ⟨λ _p _q => propext ⟨λ ⟨hp, hq⟩ => ⟨hq, hp⟩, λ ⟨hq, hp⟩ => ⟨hp, hq⟩⟩⟩
instance : IdempotentOp And := ⟨λ _p => propext ⟨λ ⟨hp, _⟩ => hp, λ hp => ⟨hp, hp⟩⟩⟩
instance : LawfulCommIdentity And True where
  right_id _p := propext ⟨λ ⟨hp, _⟩ => hp, λ hp => ⟨hp, True.intro⟩⟩

instance : Associative Or := ⟨by simp [or_assoc]⟩
instance : Commutative Or := ⟨λ_p _q => propext ⟨λ hpq => hpq.elim Or.inr Or.inl, λ hqp => hqp.elim Or.inr Or.inl⟩⟩
instance : IdempotentOp Or := ⟨λ_p => propext ⟨λ hp => hp.elim id id, Or.inl⟩⟩
instance : LawfulCommIdentity Or False where
  right_id _p := propext ⟨λ hpf => hpf.elim id False.elim, Or.inl⟩

example (x y z : Nat) : x + y + 0 + z = z + (x + y) := by ac_rfl

example (x y z : Nat) : (x + y) * (0 + z) = (x + y) * z:= by ac_rfl

example (x y z : Nat) : (x + y) * (0 + z) = 1 * z * (y + 0 + x) := by ac_rfl

theorem ex₁ (x y z : Nat) : max (0 + (max x (max z (max (0 + 0) ((max 1 0) + 0 + 0) * y)))) y = max (max x y) z := by ac_rfl
#print ex₁

example (x y : Nat) : 1 + 0 + 0 = 0 + 1 := by ac_rfl

example (x y : Nat) : (x + y = 42) = (y + x = 42) := by ac_rfl

example (x y : Nat) (P : Prop) : (x + y = 42 → P) = (y + x = 42 → P) := by ac_rfl

inductive Vector (α : Type u) : Nat → Type u where
  | nil  : Vector α 0
  | cons : α → Vector α n → Vector α (n+1)

def f (n : Nat) (xs : Vector α n) := xs

-- Repro: Dependent types trigger incorrect proofs
theorem ex₂ (n m : Nat) (xs : Vector α (n+m)) (ys : Vector α (m+n)) : (f (n+m) xs, f (m+n) ys, n+m) = (f (n+m) xs, f (m+n) ys, m+n) := by
  ac_rfl

-- Repro: Binders also trigger invalid proofs
theorem ex₃ (n : Nat) : (fun x => n + x) = (fun x => x + n) := by
  ac_rfl
#print ex₃

-- Repro: the Prop universe doesn't work
example (p q : Prop) : (p ∨ p ∨ q ∧ True) = (q ∨ p) := by
  ac_rfl

-- Repro: missing withContext
example : ∀ x : Nat, x = x := by intro x; ac_rfl
