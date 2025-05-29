-- A simple proof that should go through immediately, gets stuck due to issues with casting Nat to Int.

set_option grind.warning false
@[grind] def codelen (c: List Bool) : Int := c.length

/--
error: `grind` failed
case grind
h : ¬codelen [] = 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] ¬codelen [] = 0
    [prop] codelen [] = ↑[].length
    [prop] [].length = 0
  [eqc] False propositions
    [prop] codelen [] = 0
  [eqc] Equivalence classes
    [eqc] {codelen [], ↑[].length}
    [eqc] {[].length, 0}
  [ematch] E-matching patterns
    [thm] codelen.eq_1: [codelen #0]
    [thm] List.length_nil: [@List.length #0 (@List.nil _)]
[grind] Diagnostics
  [thm] E-Matching instances
    [thm] List.length_nil ↦ 1
    [thm] codelen.eq_1 ↦ 1
-/
#guard_msgs in
theorem issue1 : codelen [] = 0 := by grind
