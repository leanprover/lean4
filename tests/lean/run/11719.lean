/-! Regression test for Quot handling during LCNF conversion -/

namespace A

variable (α : Type)

def space : Type :=
  Quot (α := α × α) fun ⟨_, _⟩ ⟨_, _⟩ ↦ True

def subspace := { x : space α // True }

/--
warning: declaration uses `sorry`
---
warning: declaration uses `sorry`
-/
#guard_msgs in
def foo : subspace α → subspace α :=
  fun ⟨x, h⟩ ↦ x.lift sorry sorry

end A

namespace B

def space : Type :=
  Quot (α := Bool × Bool) fun ⟨_, _⟩ ⟨_, _⟩ ↦ True

def subspace := { x : space // True }

/--
warning: declaration uses `sorry`
---
warning: declaration uses `sorry`
-/
#guard_msgs in
def foo : subspace → subspace :=
  fun ⟨x, _⟩ ↦ x.lift sorry sorry

end B
