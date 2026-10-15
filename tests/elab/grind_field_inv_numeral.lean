/-!
`grind`'s ring module asserts `a * a⁻¹ = 1` or `a⁻¹ = 0` for a numeral `a` with theorems whose
numeral is `denoteInt k`, an `OfNat` numeral or its negation. The numeral recognizer must accept
these spellings only: `↑(0 : Nat)` was recognized as `0`, and `Field.inv_zero : 0⁻¹ = 0` was
pushed as a proof of `(↑0)⁻¹ = ↑0`, which the kernel rejects (see `grind_9321` with
`backward.grind.normalizer := false` before the casts were normalized). Other spellings take
the `inv_split` case split.
-/

attribute [local instance] Lean.Grind.Semiring.natCast Lean.Grind.Ring.intCast
open Lean.Grind
example {α : Type} [Field α] {z : α} : z / ↑(0 : Nat) = 0 := by grind
example {α : Type} [Field α] {z : α} : z / (-0) = 0 := by grind
example {α : Type} [Field α] {z : α} : z / (- -0) = 0 := by grind
example {α : Type} [Field α] {z : α} : z * 0⁻¹ = 0 := by grind
example {α : Type} [Field α] {z : α} : z * (-0)⁻¹ = 0 := by grind
example (z : Rat) : z * (- -3)⁻¹ * 3 = z := by grind
example (z : Rat) : z * (↑(3 : Nat))⁻¹ * 3 = z := by grind
example (z : Rat) : z * (-3)⁻¹ * 3 = -z := by grind
example {α : Type} [Field α] [IsCharP α 5] (z : α) : z * (↑(5 : Nat))⁻¹ = 0 := by grind
example {α : Type} [Field α] [IsCharP α 5] (z : α) : z * (-5)⁻¹ = 0 := by grind
example {α : Type} [Field α] [IsCharP α 5] (z : α) : z * (-3)⁻¹ * 3 = -z := by grind
