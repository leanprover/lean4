import Repro.B1
import Repro.B2

theorem baz (t : T) (h : ¬ P t) : t = t := by
  simp [P] at h
  split at h <;> rfl
