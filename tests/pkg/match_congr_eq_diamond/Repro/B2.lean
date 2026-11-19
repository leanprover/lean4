import Repro.A

/-!
The proof of `P.match_1.congr_eq_2` creates a sparse `casesOn` definition. `B1` and `B2` both
realize this equation, and `C` imports both.
-/

theorem bar (t : T) (h : ¬ P t) : t = t := by
  simp [P] at h
  split at h <;> rfl
