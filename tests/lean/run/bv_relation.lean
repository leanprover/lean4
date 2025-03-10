import Std.Tactic.BVDecide

structure State where
  x : BitVec 8
  y : BitVec 8
  z : BitVec 8

inductive Transfer : State → State → Prop
  | step : Transfer ⟨x, y, z⟩ ⟨y, z, x⟩

@[simp]
theorem Transfer.iff_x : Transfer s1 s2 ↔ (s2.x = s1.y ∧ s2.y = s1.z ∧ s2.z = s1.x) := by
  constructor
  · intro h
    cases h
    simp
  · intro h
    cases s1 <;> cases s2 <;> simp_all [Transfer.step]

def P (s : State) : Prop := s.x > 3

example : ∀ s1 s2 s3 s4, P s1 ∧ Transfer s1 s2 ∧ P s2 ∧ Transfer s2 s3 ∧ P s3 ∧ Transfer s3 s4 → P s4  := by
  simp [P]
  bv_decide
