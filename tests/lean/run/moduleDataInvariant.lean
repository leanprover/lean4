import Lean

/-!
# Test that `ModuleData.constNames_eq` invariant is usable

Verify that the `constNames_eq` field of `ModuleData` provides the expected
relationship between `constNames` and `constants`.
-/

-- The size invariant follows from the stronger name invariant.
open Lean in
example (m : ModuleData) : m.constNames.size = m.constants.size := by
  simp [m.constNames_eq]

-- Safe indexing into `constants` given a bound on `constNames`.
open Lean in
example (m : ModuleData) (i : Nat) (h : i < m.constNames.size) :
    m.constants[i]'(by simp [m.constNames_eq] at h; exact h) =
    m.constants[i]'(by simp [m.constNames_eq] at h; exact h) := rfl
