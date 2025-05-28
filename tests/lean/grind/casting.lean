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
    [prop] { toList := [] }.toList.length = 0
    [prop] [].length = 0
    [prop] { toList := [] }.toList.length = 0
  [eqc] False propositions
    [prop] codelen [] = 0
  [eqc] Equivalence classes
    [eqc] {codelen [], ↑[].length}
    [eqc] {{ toList := [] }.toList, []}
    [eqc] {{ toList := [] }.toList.length, [].length, 0}
  [ematch] E-matching patterns
    [thm] codelen.eq_1: [codelen #0]
    [thm] Array.size_empty: [@List.length #0 (@List.nil _)]
    [thm] List.size_toArray: [@List.length #1 #0]
    [thm] List.length_nil: [@List.length #0 (@List.nil _)]
    [thm] Array.length_toList: [@List.length #1 (@Array.toList _ #0)]
    [thm] Array.eq_empty_of_size_eq_zero: [@List.length #2 (@Array.toList _ #1)]
    [thm] Array.size_eq_zero_iff: [@List.length #1 (@Array.toList _ #0)]
    [thm] Vector.toArray_empty: [@Array.mk #0 (@List.nil _)]
    [thm] Array.toArray_toList: [@Array.mk #1 (@Array.toList _ #0)]
[grind] Diagnostics
  [thm] E-Matching instances
    [thm] Array.eq_empty_of_size_eq_zero ↦ 1
    [thm] Array.length_toList ↦ 1
    [thm] Array.size_empty ↦ 1
    [thm] Array.size_eq_zero_iff ↦ 1
    [thm] Array.toArray_toList ↦ 1
    [thm] List.length_nil ↦ 1
    [thm] List.size_toArray ↦ 1
    [thm] Vector.toArray_empty ↦ 1
    [thm] codelen.eq_1 ↦ 1
-/
#guard_msgs in
theorem issue1 : codelen [] = 0 := by grind
