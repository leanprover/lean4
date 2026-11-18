/-!
Operands of `≤` and `<` in a ring must be visible to the ring module, so that it propagates
equalities between them. With the `Sym.simp` normalizer, `b + b + d` is normalized to `2 * b + d`,
and `a ≤ b + c + d` is no longer congruent to the goal after `c = b`; the ring module has to relate
`b + c + d` and `2 * b + d`. Linarith cannot help here: it ignores negated facts on preorders, and
`<` facts without `LawfulOrderLT`.
-/

set_option backward.grind.normalizer false
open Std Lean Grind

example [CommRing α] [LE α] [LT α] [IsLinearOrder α] [OrderedRing α] (a b c d : α)
    : a < b + c + d → c = b → a < b + b + d := by
  grind

example [CommRing α] [LE α] [LT α] [IsPreorder α] [OrderedRing α] (a b c d : α)
    : c = b → a ≤ b + c + d → a ≤ b + b + d := by
  grind

example [CommRing α] [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α] [OrderedRing α] (a b c d : α)
    : c = b → a ≤ b + c + d → a ≤ b + b + d := by
  grind

example [CommRing α] [LE α] [LT α] [IsPreorder α] [OrderedRing α] (a b c d : α)
    : c = b → a ≤ (b + c) * d → a ≤ 2 * b * d := by
  grind
