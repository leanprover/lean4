import Lean

/-!
Tests virtual structure eta for `type_def`-declared types (`Lean.Meta.isDefEqVirtualEtaStruct`):
`N.mk (N.toNat x) = x` holds by `rfl`, just like eta for a real one-field structure, even though
`N`/`N.mk`/`N.toNat` are irreducible. Also tests that `simp only` reduces the virtual projection
`N.toNat (N.mk n)` the same way it does for a real structure's projection-of-constructor
(`Lean.Meta.reduceVirtualProj?`, wired into `Simp.reduceStep`).
-/

type_def N := Nat with toNat

-- Virtual eta.
example (x : N) : N.mk (N.toNat x) = x := rfl

-- `simp only` reduces the virtual projection (iota), without any lemmas.
example (n : Nat) : N.toNat (N.mk n) = n := by simp only
