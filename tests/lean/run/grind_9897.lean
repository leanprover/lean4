module
def Set' (α : Type u) := α → Prop

namespace Set'

protected def Mem (s : Set' α) (a : α) : Prop :=
  s a

instance : Membership α (Set' α) :=
  ⟨Set'.Mem⟩

end Set'

def Ioi' [LT α] (a : α) : Set' α := fun x => a < x

@[grind =] theorem mem_Ioi [LT α] {x a : α} : x ∈ Ioi' a ↔ a < x := Iff.rfl

theorem ProbabilityTheory.crash.extracted_1_3
    [LE α] [LT α] [Std.LawfulOrderLT α] [DecidableEq α]
    [Lean.Grind.Ring α] [Std.IsLinearOrder α] [Lean.Grind.OrderedRing α] (X : α → α)
  (hnonneg : ∀ (i : α), 0 ≤ X i) (n : α) (hn : X n ∉ Ioi' 0) :
  (if n = X n then 0 else 0) + X n = 0 := by grind
