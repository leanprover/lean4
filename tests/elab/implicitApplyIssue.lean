def Set α := α → Prop

class HasMem (α : outParam $ Type u) (β : Type v) where
    mem : α → β → Prop

infix:50 " ∈ " => HasMem.mem

instance {α : Type u} : HasMem α (Set α) := ⟨λ a s => s a⟩

instance {α : Type u} : LE (Set α) := ⟨λ s t => ∀ {x : α}, x ∈ s → x ∈ t⟩

class HasInf (P : Type u) where
  inf : P → P → P

infix:70 " ⊓ " => HasInf.inf

instance {α : Type u} : HasInf (Set α) := ⟨λ s t x => x ∈ s ∧ x ∈ t⟩

theorem infLeLeft {s t : Set α} : s ⊓ t ≤ s := And.left
theorem infLeRight {s t : Set α} : s ⊓ t ≤ t := And.right

theorem inter_mem_sets_iff {α : Type u} (f : Set (Set α)) (hf : ∀ {s t}, s ∈ f → s ≤ t → t ∈ f) {x y : Set α}
        : x ⊓ y ∈ f → x ∈ f ∧ y ∈ f := by
  intro h
  refine ⟨hf h infLeLeft, hf h ?_⟩
  apply infLeRight
