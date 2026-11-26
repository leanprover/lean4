/-!
`linarith` treats a product with a numeral, such as `2 * c`, as a scaled variable rather than as
an atom: `isHomoMulInst` compared the multiplication function with its instance, and `isNumeral`
expected a nested `OfNat.ofNat` literal.
-/
open Lean Grind Std

variable [CommRing α] [LE α] [LT α] [LawfulOrderLT α] [IsLinearOrder α] [OrderedRing α]

/--
trace: [grind.debug.linarith.search.assign] One.one := 1
[grind.debug.linarith.search.assign] b := 0
[grind.debug.linarith.search.assign] c := 0
[grind.debug.linarith.search.assign] a := 1
-/
#guard_msgs (trace, drop error) in
set_option trace.grind.debug.linarith.search.assign true in
example (a b c : α) : a ≠ b + 2 * c → a > b + c → False := by
  grind

-- Model-based theory combination evaluates `2 * c` from the assignment of `c`.
example (f : α → Nat) (a c : α) (h₁ : a ≤ 2 * c) (h₂ : 2 * c ≤ a) : f a = f (2 * c) := by grind
example (f : α → Nat) (a c : α) (h₁ : a ≤ c + c) (h₂ : c + c ≤ a) : f a = f (2 * c) := by grind
example (f : α → Nat) (a c : α) (h₁ : a ≤ c + c) (h₂ : c + c ≤ a) : f a = f (c * 2) := by grind
example (f : α → Nat) (a c : α) (h₁ : a ≤ -2 * c) (h₂ : -2 * c ≤ a) : f a = f (-2 * c) := by grind
