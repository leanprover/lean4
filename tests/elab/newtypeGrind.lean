import Lean

/-!
Confirms `grind` needs no `newtype`-specific special-casing of its own: its simp-based
normalization (`Lean.Meta.Grind.simpCore`/`dsimpCore`) reuses `Simp.mainCore`/`Simp.reduceStep`,
which already knows how to reduce virtual projections (see `newtypeVirtualIota.lean`).
-/

newtype N := Nat with toNat

example (n : Nat) : N.toNat (N.mk n) = n := by grind
