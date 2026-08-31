class HasMem (α : outParam $ Type u) (β : Type v) where
    mem : α → β → Prop

class PartialOrder (P : Type u) extends LE P where
  refl (s : P) : s ≤ s
  antisymm (s t : P) : s ≤ t → t ≤ s → s = t
  trans (s t u : P) : s ≤ t → t ≤ u → s ≤ u

theorem LE.le.trans {P : Type _} [PartialOrder P] {x y z : P} : x ≤ y → y ≤ z → x ≤ z := PartialOrder.trans _ _ _

infix:50 " ∈ " => HasMem.mem

def Set (α : Type u) := α → Prop

namespace Set

instance : HasMem α (Set α) := ⟨λ a s => s a⟩

theorem ext {s t : Set α} (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t :=
  funext $ λ x => propext $ h x

instance : LE (Set α) := ⟨λ s t => ∀ {x : α}, x ∈ s → x ∈ t⟩

instance : PartialOrder (Set α) where
  refl := λ s x => id
  antisymm := λ s t hst hts => ext $ λ x => ⟨hst, hts⟩
  trans := λ s t u hst htu x hxs => htu $ hst hxs

variable (x y z : Set α) (hxy : x ≤ y) (hyz : y ≤ z)

example : x ≤ z := hxy.trans hyz

example : x ≤ z := by
  refine hxy.trans ?_
  exact hyz

example : x ≤ z := by
  apply hxy.trans
  assumption

example : x ≤ y → y ≤ z → x ≤ z :=
  λ h h' => _ -- goal view has the unfolded `x✝ ∈ x → x✝ ∈ z` instead of `x ≤ y`
