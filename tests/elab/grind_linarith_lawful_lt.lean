/-!
`grind linarith` must not use `<` on a type without a `LawfulOrderLT` instance: every theorem it
has about `<` assumes it. Such `<` facts, negated facts, and disequality splits are now ignored, and
`grind` fails normally instead of throwing "structure does not have a lawful LT instance" or
"structure does not support LT" while constructing the proof.

Found with the `Sym.simp` normalizer: the legacy normalizer closes the first example by congruence
(`c = b` makes `b + c + d` and `b + b + d` congruent), while `Sym.simp` rewrites `b + b + d` to
`2 * b + d`, so linarith combined two `<` facts. The ring module now relates `b + c + d` and
`2 * b + d` itself, so the example is proved with either normalizer.
-/

open Std Lean Grind

section
set_option backward.grind.normalizer false

example [CommRing α] [LE α] [LT α] [IsLinearOrder α] [OrderedRing α] (a b c d : α)
    : a < b + c + d → c = b → a < b + b + d := by
  grind

example [CommRing α] [LE α] [LT α] [LawfulOrderLT α] [IsLinearOrder α] [OrderedRing α] (a b c d : α)
    : a < b + c + d → c = b → a < b + b + d := by
  grind

end

-- Independent of the normalizer
/--
error: `grind` failed
case grind
α : Type u_1
inst : IntModule α
inst_1 : LE α
inst_2 : LT α
inst_3 : IsLinearOrder α
inst_4 : OrderedAdd α
a b c : α
h : a < b
h_1 : b < c
h_2 : ¬a < c
⊢ False
use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example [IntModule α] [LE α] [LT α] [IsLinearOrder α] [OrderedAdd α] (a b c : α)
    : a < b → b < c → a < c := by
  grind -verbose

-- Disequality split on a type without `LT`
/--
error: `grind` failed
case grind
α : Type u_1
inst : IntModule α
inst_1 : LE α
inst_2 : IsLinearOrder α
inst_3 : OrderedAdd α
a b c : α
h : a ≤ c
h_1 : c ≤ b
h_2 : b ≤ a
h_3 : ¬a + b = 2 • c
⊢ False
use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example [IntModule α] [LE α] [IsLinearOrder α] [OrderedAdd α] (a b c : α)
    : a ≤ c → c ≤ b → b ≤ a → a + b ≠ 2 • c → False := by
  grind -verbose

example [IntModule α] [LE α] [LT α] [LawfulOrderLT α] [IsLinearOrder α] [OrderedAdd α] (a b c : α)
    : a < b → b < c → a < c := by
  grind

example [IntModule α] [LE α] [LT α] [LawfulOrderLT α] [IsLinearOrder α] [OrderedAdd α] (a b c : α)
    : a ≤ c → c ≤ b → b ≤ a → a + b ≠ 2 • c → False := by
  grind
