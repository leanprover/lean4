open Sum Function

-- This needs to be in the library!
-- https://github.com/leanprover/lean4/pull/11085
attribute [grind =] Prod.map_fst Prod.map_snd

-- Copy the definition of `Equiv` from Mathlib.
structure Equiv (α : Sort _) (β : Sort _) where
  protected toFun : α → β
  protected invFun : β → α
  protected left_inv : LeftInverse invFun toFun := by intro; first | rfl | ext <;> rfl
  protected right_inv : RightInverse invFun toFun := by intro; first | rfl | ext <;> rfl

infixl:25 " ≃ " => Equiv

def sumProdDistrib (α β γ) : (α ⊕ β) × γ ≃ α × γ ⊕ β × γ :=
  ⟨fun p => p.1.map (fun x => (x, p.2)) fun x => (x, p.2),
    fun s => s.elim (Prod.map inl id) (Prod.map inr id), by
      rintro ⟨_ | _, _⟩ <;> rfl, by
      rintro (⟨_, _⟩ | ⟨_, _⟩)
      · grind
      · grind⟩

def sumProdDistrib' (α β γ) : (α ⊕ β) × γ ≃ α × γ ⊕ β × γ :=
  ⟨fun p => p.1.map (fun x => (x, p.2)) fun x => (x, p.2),
    fun s => s.elim (Prod.map inl id) (Prod.map inr id), by
      rintro ⟨_ | _, _⟩ <;> rfl, by
      rintro (⟨_, _⟩ | ⟨_, _⟩)
      · grind +abstractProof
      · grind +abstractProof⟩

def sumProdDistrib'' (α β γ) : (α ⊕ β) × γ ≃ α × γ ⊕ β × γ :=
  ⟨fun p => p.1.map (fun x => (x, p.2)) fun x => (x, p.2),
    fun s => s.elim (Prod.map inl id) (Prod.map inr id), by
      rintro ⟨_ | _, _⟩ <;> rfl, by
      rintro (⟨_, _⟩ | ⟨_, _⟩)
      · grind?
      · grind?⟩

example (α β γ) (fst : α) (snd : γ) :
    (fun p : (α ⊕ β) × γ ↦ Sum.map (fun x ↦ (x, p.snd)) (fun x ↦ (x, p.snd)) p.fst)
      ((fun s ↦ Sum.elim (Prod.map inl id) (Prod.map inr id) s) (inl (fst, snd))) =
    inl (fst, snd) := by
  grind

example (α β γ) :
    RightInverse (fun s : α × γ ⊕ β × γ ↦ Sum.elim (Prod.map inl id) (Prod.map inr id) s) fun p ↦
      Sum.map (fun x ↦ (x, p.snd)) (fun x ↦ (x, p.snd)) p.fst := by
  rintro (⟨_, _⟩ | ⟨_, _⟩) <;> grind
