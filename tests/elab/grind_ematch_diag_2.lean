module

public section

/-! This module tests the new grind ematching diagnostics through a small example ported from Viper -/

axiom Slice : Type
axiom Address : Type
axiom Heap : Type

axiom slot : Slice → Nat → Address
axiom lookup : Heap → Address → Nat
axiom next : Address → Address

set_option warn.sorry false


theorem inj : ∀ slice i j, i ≠ j → slot slice i ≠ slot slice j := sorry

grind_pattern inj => slot slice i, slot slice j where
  i =/= j

theorem next_def : ∀ slice i, next (slot slice i) = slot slice (i + 1) := sorry

grind_pattern next_def => slot slice i

axiom heap : Heap
axiom s : Slice
axiom idx : Nat
axiom len : Nat

theorem sorted : ∀ i, i < len → lookup heap (slot s i) ≤ lookup heap (next (slot s i)) := sorry

grind_pattern sorted => lookup heap (slot s i)

/--
error: `grind` failed
case grind.1.1.1.1.1.1.1
h1 : idx < len
h : lookup heap (next (slot s idx)) ≤ lookup heap (slot s idx)
h_1 : idx + 2 ≤ len
h_2 : idx + 3 ≤ len
h_3 : idx + 4 ≤ len
h_4 : idx + 5 ≤ len
h_5 : idx + 6 ≤ len
h_6 : idx + 7 ≤ len
h_7 : idx + 8 ≤ len
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] idx + 1 ≤ len
    [prop] lookup heap (next (slot s idx)) ≤ lookup heap (slot s idx)
    [prop] next (slot s idx) = slot s (idx + 1)
    [prop] idx + 1 ≤ len → lookup heap (slot s idx) ≤ lookup heap (next (slot s idx))
    [prop] next (slot s (idx + 1)) = slot s (idx + 2)
    [prop] ¬slot s (idx + 1) = slot s idx
    [prop] ¬slot s idx = slot s (idx + 1)
    [prop] idx + 2 ≤ len → lookup heap (slot s (idx + 1)) ≤ lookup heap (next (slot s (idx + 1)))
    [prop] next (slot s (idx + 2)) = slot s (idx + 3)
    [prop] ¬slot s (idx + 2) = slot s idx
    [prop] ¬slot s (idx + 2) = slot s (idx + 1)
    [prop] ¬slot s idx = slot s (idx + 2)
    [prop] ¬slot s (idx + 1) = slot s (idx + 2)
    [prop] idx + 3 ≤ len → lookup heap (slot s (idx + 2)) ≤ lookup heap (next (slot s (idx + 2)))
    [prop] next (slot s (idx + 3)) = slot s (idx + 4)
    [prop] ¬slot s (idx + 3) = slot s idx
    [prop] ¬slot s (idx + 3) = slot s (idx + 1)
    [prop] ¬slot s (idx + 3) = slot s (idx + 2)
    [prop] ¬slot s idx = slot s (idx + 3)
    [prop] ¬slot s (idx + 1) = slot s (idx + 3)
    [prop] ¬slot s (idx + 2) = slot s (idx + 3)
    [prop] idx + 4 ≤ len → lookup heap (slot s (idx + 3)) ≤ lookup heap (next (slot s (idx + 3)))
    [prop] next (slot s (idx + 4)) = slot s (idx + 5)
    [prop] ¬slot s (idx + 4) = slot s idx
    [prop] ¬slot s (idx + 4) = slot s (idx + 1)
    [prop] ¬slot s (idx + 4) = slot s (idx + 2)
    [prop] ¬slot s (idx + 4) = slot s (idx + 3)
    [prop] ¬slot s idx = slot s (idx + 4)
    [prop] ¬slot s (idx + 1) = slot s (idx + 4)
    [prop] ¬slot s (idx + 2) = slot s (idx + 4)
    [prop] ¬slot s (idx + 3) = slot s (idx + 4)
    [prop] idx + 5 ≤ len → lookup heap (slot s (idx + 4)) ≤ lookup heap (next (slot s (idx + 4)))
    [prop] idx + 2 ≤ len
    [prop] next (slot s (idx + 5)) = slot s (idx + 6)
    [prop] ¬slot s (idx + 5) = slot s idx
    [prop] ¬slot s (idx + 5) = slot s (idx + 1)
    [prop] ¬slot s (idx + 5) = slot s (idx + 2)
    [prop] ¬slot s (idx + 5) = slot s (idx + 3)
    [prop] ¬slot s (idx + 5) = slot s (idx + 4)
    [prop] ¬slot s idx = slot s (idx + 5)
    [prop] ¬slot s (idx + 1) = slot s (idx + 5)
    [prop] ¬slot s (idx + 2) = slot s (idx + 5)
    [prop] ¬slot s (idx + 3) = slot s (idx + 5)
    [prop] ¬slot s (idx + 4) = slot s (idx + 5)
    [prop] idx + 6 ≤ len → lookup heap (slot s (idx + 5)) ≤ lookup heap (next (slot s (idx + 5)))
    [prop] next (slot s (idx + 6)) = slot s (idx + 7)
    [prop] ¬slot s (idx + 6) = slot s idx
    [prop] ¬slot s (idx + 6) = slot s (idx + 1)
    [prop] ¬slot s (idx + 6) = slot s (idx + 2)
    [prop] ¬slot s (idx + 6) = slot s (idx + 3)
    [prop] ¬slot s (idx + 6) = slot s (idx + 4)
    [prop] ¬slot s (idx + 6) = slot s (idx + 5)
    [prop] ¬slot s idx = slot s (idx + 6)
    [prop] ¬slot s (idx + 1) = slot s (idx + 6)
    [prop] ¬slot s (idx + 2) = slot s (idx + 6)
    [prop] ¬slot s (idx + 3) = slot s (idx + 6)
    [prop] ¬slot s (idx + 4) = slot s (idx + 6)
    [prop] ¬slot s (idx + 5) = slot s (idx + 6)
    [prop] idx + 7 ≤ len → lookup heap (slot s (idx + 6)) ≤ lookup heap (next (slot s (idx + 6)))
    [prop] next (slot s (idx + 7)) = slot s (idx + 8)
    [prop] ¬slot s (idx + 7) = slot s idx
    [prop] ¬slot s (idx + 7) = slot s (idx + 1)
    [prop] ¬slot s (idx + 7) = slot s (idx + 2)
    [prop] ¬slot s (idx + 7) = slot s (idx + 3)
    [prop] ¬slot s (idx + 7) = slot s (idx + 4)
    [prop] ¬slot s (idx + 7) = slot s (idx + 5)
    [prop] ¬slot s (idx + 7) = slot s (idx + 6)
    [prop] ¬slot s idx = slot s (idx + 7)
    [prop] ¬slot s (idx + 1) = slot s (idx + 7)
    [prop] ¬slot s (idx + 2) = slot s (idx + 7)
    [prop] ¬slot s (idx + 3) = slot s (idx + 7)
    [prop] ¬slot s (idx + 4) = slot s (idx + 7)
    [prop] ¬slot s (idx + 5) = slot s (idx + 7)
    [prop] ¬slot s (idx + 6) = slot s (idx + 7)
    [prop] idx + 8 ≤ len → lookup heap (slot s (idx + 7)) ≤ lookup heap (next (slot s (idx + 7)))
    [prop] idx + 3 ≤ len
    [prop] idx + 4 ≤ len
    [prop] idx + 5 ≤ len
    [prop] idx + 6 ≤ len
    [prop] idx + 7 ≤ len
    [prop] idx + 8 ≤ len
  [eqc] True propositions
    [prop] lookup heap (next (slot s idx)) ≤ lookup heap (slot s idx)
    [prop] idx + 1 ≤ len
    [prop] lookup heap (slot s idx) ≤ lookup heap (next (slot s idx))
    [prop] idx + 1 ≤ len → lookup heap (slot s idx) ≤ lookup heap (next (slot s idx))
    [prop] lookup heap (slot s (idx + 1)) ≤ lookup heap (next (slot s (idx + 1)))
    [prop] idx + 2 ≤ len
    [prop] idx + 2 ≤ len → lookup heap (slot s (idx + 1)) ≤ lookup heap (next (slot s (idx + 1)))
    [prop] lookup heap (slot s (idx + 2)) ≤ lookup heap (next (slot s (idx + 2)))
    [prop] idx + 3 ≤ len
    [prop] idx + 3 ≤ len → lookup heap (slot s (idx + 2)) ≤ lookup heap (next (slot s (idx + 2)))
    [prop] lookup heap (slot s (idx + 3)) ≤ lookup heap (next (slot s (idx + 3)))
    [prop] idx + 4 ≤ len
    [prop] idx + 4 ≤ len → lookup heap (slot s (idx + 3)) ≤ lookup heap (next (slot s (idx + 3)))
    [prop] lookup heap (slot s (idx + 4)) ≤ lookup heap (next (slot s (idx + 4)))
    [prop] idx + 5 ≤ len
    [prop] idx + 5 ≤ len → lookup heap (slot s (idx + 4)) ≤ lookup heap (next (slot s (idx + 4)))
    [prop] lookup heap (slot s (idx + 5)) ≤ lookup heap (next (slot s (idx + 5)))
    [prop] idx + 6 ≤ len
    [prop] idx + 6 ≤ len → lookup heap (slot s (idx + 5)) ≤ lookup heap (next (slot s (idx + 5)))
    [prop] lookup heap (slot s (idx + 6)) ≤ lookup heap (next (slot s (idx + 6)))
    [prop] idx + 7 ≤ len
    [prop] idx + 7 ≤ len → lookup heap (slot s (idx + 6)) ≤ lookup heap (next (slot s (idx + 6)))
    [prop] lookup heap (slot s (idx + 7)) ≤ lookup heap (next (slot s (idx + 7)))
    [prop] idx + 8 ≤ len
    [prop] idx + 8 ≤ len → lookup heap (slot s (idx + 7)) ≤ lookup heap (next (slot s (idx + 7)))
  [eqc] False propositions
    [prop] slot s idx = slot s (idx + 1)
    [prop] slot s (idx + 1) = slot s idx
    [prop] slot s idx = slot s (idx + 2)
    [prop] slot s (idx + 1) = slot s (idx + 2)
    [prop] slot s (idx + 2) = slot s idx
    [prop] slot s (idx + 2) = slot s (idx + 1)
    [prop] slot s idx = slot s (idx + 3)
    [prop] slot s (idx + 1) = slot s (idx + 3)
    [prop] slot s (idx + 2) = slot s (idx + 3)
    [prop] slot s (idx + 3) = slot s idx
    [prop] slot s (idx + 3) = slot s (idx + 1)
    [prop] slot s (idx + 3) = slot s (idx + 2)
    [prop] slot s idx = slot s (idx + 4)
    [prop] slot s (idx + 1) = slot s (idx + 4)
    [prop] slot s (idx + 2) = slot s (idx + 4)
    [prop] slot s (idx + 3) = slot s (idx + 4)
    [prop] slot s (idx + 4) = slot s idx
    [prop] slot s (idx + 4) = slot s (idx + 1)
    [prop] slot s (idx + 4) = slot s (idx + 2)
    [prop] slot s (idx + 4) = slot s (idx + 3)
    [prop] slot s idx = slot s (idx + 5)
    [prop] slot s (idx + 1) = slot s (idx + 5)
    [prop] slot s (idx + 2) = slot s (idx + 5)
    [prop] slot s (idx + 3) = slot s (idx + 5)
    [prop] slot s (idx + 4) = slot s (idx + 5)
    [prop] slot s (idx + 5) = slot s idx
    [prop] slot s (idx + 5) = slot s (idx + 1)
    [prop] slot s (idx + 5) = slot s (idx + 2)
    [prop] slot s (idx + 5) = slot s (idx + 3)
    [prop] slot s (idx + 5) = slot s (idx + 4)
    [prop] slot s idx = slot s (idx + 6)
    [prop] slot s (idx + 1) = slot s (idx + 6)
    [prop] slot s (idx + 2) = slot s (idx + 6)
    [prop] slot s (idx + 3) = slot s (idx + 6)
    [prop] slot s (idx + 4) = slot s (idx + 6)
    [prop] slot s (idx + 5) = slot s (idx + 6)
    [prop] slot s (idx + 6) = slot s idx
    [prop] slot s (idx + 6) = slot s (idx + 1)
    [prop] slot s (idx + 6) = slot s (idx + 2)
    [prop] slot s (idx + 6) = slot s (idx + 3)
    [prop] slot s (idx + 6) = slot s (idx + 4)
    [prop] slot s (idx + 6) = slot s (idx + 5)
    [prop] slot s idx = slot s (idx + 7)
    [prop] slot s (idx + 1) = slot s (idx + 7)
    [prop] slot s (idx + 2) = slot s (idx + 7)
    [prop] slot s (idx + 3) = slot s (idx + 7)
    [prop] slot s (idx + 4) = slot s (idx + 7)
    [prop] slot s (idx + 5) = slot s (idx + 7)
    [prop] slot s (idx + 6) = slot s (idx + 7)
    [prop] slot s (idx + 7) = slot s idx
    [prop] slot s (idx + 7) = slot s (idx + 1)
    [prop] slot s (idx + 7) = slot s (idx + 2)
    [prop] slot s (idx + 7) = slot s (idx + 3)
    [prop] slot s (idx + 7) = slot s (idx + 4)
    [prop] slot s (idx + 7) = slot s (idx + 5)
    [prop] slot s (idx + 7) = slot s (idx + 6)
  [eqc] Equivalence classes
    [eqc] {next (slot s idx), slot s (idx + 1)}
    [eqc] {lookup heap (next (slot s idx)), lookup heap (slot s idx), lookup heap (slot s (idx + 1))}
    [eqc] {next (slot s (idx + 1)), slot s (idx + 2)}
    [eqc] {lookup heap (next (slot s (idx + 1))), lookup heap (slot s (idx + 2))}
    [eqc] {next (slot s (idx + 2)), slot s (idx + 3)}
    [eqc] {lookup heap (next (slot s (idx + 2))), lookup heap (slot s (idx + 3))}
    [eqc] {next (slot s (idx + 3)), slot s (idx + 4)}
    [eqc] {lookup heap (next (slot s (idx + 3))), lookup heap (slot s (idx + 4))}
    [eqc] {next (slot s (idx + 4)), slot s (idx + 5)}
    [eqc] {lookup heap (next (slot s (idx + 4))), lookup heap (slot s (idx + 5))}
    [eqc] {next (slot s (idx + 5)), slot s (idx + 6)}
    [eqc] {lookup heap (next (slot s (idx + 5))), lookup heap (slot s (idx + 6))}
    [eqc] {next (slot s (idx + 6)), slot s (idx + 7)}
    [eqc] {lookup heap (next (slot s (idx + 6))), lookup heap (slot s (idx + 7))}
    [eqc] {next (slot s (idx + 7)), slot s (idx + 8)}
    [eqc] others
      [eqc] {↑(lookup heap (next (slot s idx))), ↑(lookup heap (slot s idx)), ↑(lookup heap (slot s (idx + 1)))}
      [eqc] {↑(lookup heap (next (slot s (idx + 1)))), ↑(lookup heap (slot s (idx + 2)))}
      [eqc] {↑(lookup heap (next (slot s (idx + 2)))), ↑(lookup heap (slot s (idx + 3)))}
      [eqc] {↑(lookup heap (next (slot s (idx + 3)))), ↑(lookup heap (slot s (idx + 4)))}
      [eqc] {↑(lookup heap (next (slot s (idx + 4)))), ↑(lookup heap (slot s (idx + 5)))}
      [eqc] {↑(lookup heap (next (slot s (idx + 5)))), ↑(lookup heap (slot s (idx + 6)))}
      [eqc] {↑(lookup heap (next (slot s (idx + 6)))), ↑(lookup heap (slot s (idx + 7)))}
  [cases] Case analyses
    [cases] [1/2]: idx + 2 ≤ len
      [cases] source: E-matching `sorted`
    [cases] [1/2]: idx + 3 ≤ len
      [cases] source: E-matching `sorted`
    [cases] [1/2]: idx + 4 ≤ len
      [cases] source: E-matching `sorted`
    [cases] [1/2]: idx + 5 ≤ len
      [cases] source: E-matching `sorted`
    [cases] [1/2]: idx + 6 ≤ len
      [cases] source: E-matching `sorted`
    [cases] [1/2]: idx + 7 ≤ len
      [cases] source: E-matching `sorted`
    [cases] [1/2]: idx + 8 ≤ len
      [cases] source: E-matching `sorted`
  [ematch] E-matching patterns
    [thm] next_def: [slot #1 #0]
    [thm] inj: [slot #3 #2, slot #3 #1]
    [thm] sorted: [lookup `[heap] (slot `[s] #1)]
  [cutsat] Assignment satisfying linear constraints
    [assign] idx := 0
    [assign] len := 8
    [assign] lookup heap (next (slot s idx)) := 0
    [assign] lookup heap (slot s idx) := 0
    [assign] lookup heap (next (slot s (idx + 1))) := 0
    [assign] lookup heap (slot s (idx + 1)) := 0
    [assign] lookup heap (next (slot s (idx + 2))) := 0
    [assign] lookup heap (slot s (idx + 2)) := 0
    [assign] lookup heap (next (slot s (idx + 3))) := 0
    [assign] lookup heap (slot s (idx + 3)) := 0
    [assign] lookup heap (next (slot s (idx + 4))) := 0
    [assign] lookup heap (slot s (idx + 4)) := 0
    [assign] lookup heap (next (slot s (idx + 5))) := 0
    [assign] lookup heap (slot s (idx + 5)) := 0
    [assign] lookup heap (next (slot s (idx + 6))) := 0
    [assign] lookup heap (slot s (idx + 6)) := 0
    [assign] lookup heap (next (slot s (idx + 7))) := 0
    [assign] lookup heap (slot s (idx + 7)) := 0
  [ring] Ring `Int`
    [basis] Basis
      [_] ↑(lookup heap (next (slot s idx))) + -1 * ↑(lookup heap (slot s idx)) = 0
      [_] ↑(lookup heap (slot s idx)) + -1 * ↑(lookup heap (slot s (idx + 1))) = 0
      [_] ↑(lookup heap (next (slot s (idx + 1)))) + -1 * ↑(lookup heap (slot s (idx + 2))) = 0
      [_] ↑(lookup heap (next (slot s (idx + 2)))) + -1 * ↑(lookup heap (slot s (idx + 3))) = 0
      [_] ↑(lookup heap (next (slot s (idx + 3)))) + -1 * ↑(lookup heap (slot s (idx + 4))) = 0
      [_] ↑(lookup heap (next (slot s (idx + 4)))) + -1 * ↑(lookup heap (slot s (idx + 5))) = 0
      [_] ↑(lookup heap (next (slot s (idx + 5)))) + -1 * ↑(lookup heap (slot s (idx + 6))) = 0
      [_] ↑(lookup heap (next (slot s (idx + 6)))) + -1 * ↑(lookup heap (slot s (idx + 7))) = 0
  [limits] Thresholds reached
    [limit] maximum term generation has been reached, threshold: `(gen := 8)`
[grind] Diagnostics
  [ematch] E-matching Diagnostics
    [thm] Theorem Instance Count
      [thm] inj ↦ 56
      [thm] next_def ↦ 8
      [thm] sorted ↦ 8
    [thm] High Cost Instances
      [thm] next_def : next (slot s idx) = slot s (idx + 1) ↦ 69.015625
      [thm] next_def : next (slot s (idx + 1)) = slot s (idx + 1 + 1) ↦ 60.015625
      [thm] next_def : next (slot s (idx + 2)) = slot s (idx + 2 + 1) ↦ 50.031250
      [thm] next_def : next (slot s (idx + 3)) = slot s (idx + 3 + 1) ↦ 40.062500
      [thm] next_def : next (slot s (idx + 4)) = slot s (idx + 4 + 1) ↦ 30.125000
      [thm] next_def : next (slot s (idx + 5)) = slot s (idx + 5 + 1) ↦ 20.250000
      [thm] next_def : next (slot s (idx + 6)) = slot s (idx + 6 + 1) ↦ 10.500000
    [thm] Excessively Branching Instances
      [thm] next_def: next (slot s (idx + 1)) = slot s (idx + 1 + 1) has 16 direct follow up instances
        [thm] sorted: idx + 2 < len → lookup heap (slot s (idx + 2)) ≤ lookup heap (next (slot s (idx + 2)))
        [thm] inj: idx + 2 ≠ idx + 7 → slot s (idx + 2) ≠ slot s (idx + 7)
        [thm] inj: idx + 2 ≠ idx + 5 → slot s (idx + 2) ≠ slot s (idx + 5)
        [thm] inj: idx ≠ idx + 2 → slot s idx ≠ slot s (idx + 2)
        [thm] inj: idx + 6 ≠ idx + 2 → slot s (idx + 6) ≠ slot s (idx + 2)
        [thm] inj: idx + 1 ≠ idx + 2 → slot s (idx + 1) ≠ slot s (idx + 2)
        [thm] inj: idx + 2 ≠ idx + 6 → slot s (idx + 2) ≠ slot s (idx + 6)
        [thm] inj: idx + 2 ≠ idx + 1 → slot s (idx + 2) ≠ slot s (idx + 1)
        [thm] inj: idx + 2 ≠ idx + 4 → slot s (idx + 2) ≠ slot s (idx + 4)
        [thm] inj: idx + 2 ≠ idx + 3 → slot s (idx + 2) ≠ slot s (idx + 3)
        [thm] inj: idx + 5 ≠ idx + 2 → slot s (idx + 5) ≠ slot s (idx + 2)
        [thm] inj: idx + 7 ≠ idx + 2 → slot s (idx + 7) ≠ slot s (idx + 2)
        [thm] inj: idx + 2 ≠ idx → slot s (idx + 2) ≠ slot s idx
        [thm] inj: idx + 3 ≠ idx + 2 → slot s (idx + 3) ≠ slot s (idx + 2)
        [thm] next_def: next (slot s (idx + 2)) = slot s (idx + 2 + 1)
        [thm] inj: idx + 4 ≠ idx + 2 → slot s (idx + 4) ≠ slot s (idx + 2)
      [thm] next_def: next (slot s (idx + 2)) = slot s (idx + 2 + 1) has 16 direct follow up instances
        [thm] inj: idx + 3 ≠ idx + 5 → slot s (idx + 3) ≠ slot s (idx + 5)
        [thm] next_def: next (slot s (idx + 3)) = slot s (idx + 3 + 1)
        [thm] inj: idx + 1 ≠ idx + 3 → slot s (idx + 1) ≠ slot s (idx + 3)
        [thm] inj: idx + 4 ≠ idx + 3 → slot s (idx + 4) ≠ slot s (idx + 3)
        [thm] inj: idx + 3 ≠ idx → slot s (idx + 3) ≠ slot s idx
        [thm] sorted: idx + 3 < len → lookup heap (slot s (idx + 3)) ≤ lookup heap (next (slot s (idx + 3)))
        [thm] inj: idx ≠ idx + 3 → slot s idx ≠ slot s (idx + 3)
        [thm] inj: idx + 5 ≠ idx + 3 → slot s (idx + 5) ≠ slot s (idx + 3)
        [thm] inj: idx + 3 ≠ idx + 6 → slot s (idx + 3) ≠ slot s (idx + 6)
        [thm] inj: idx + 3 ≠ idx + 1 → slot s (idx + 3) ≠ slot s (idx + 1)
        [thm] inj: idx + 2 ≠ idx + 3 → slot s (idx + 2) ≠ slot s (idx + 3)
        [thm] inj: idx + 6 ≠ idx + 3 → slot s (idx + 6) ≠ slot s (idx + 3)
        [thm] inj: idx + 3 ≠ idx + 2 → slot s (idx + 3) ≠ slot s (idx + 2)
        [thm] inj: idx + 7 ≠ idx + 3 → slot s (idx + 7) ≠ slot s (idx + 3)
        [thm] inj: idx + 3 ≠ idx + 7 → slot s (idx + 3) ≠ slot s (idx + 7)
        [thm] inj: idx + 3 ≠ idx + 4 → slot s (idx + 3) ≠ slot s (idx + 4)
      [thm] next_def: next (slot s (idx + 3)) = slot s (idx + 3 + 1) has 16 direct follow up instances
        [thm] inj: idx + 4 ≠ idx + 1 → slot s (idx + 4) ≠ slot s (idx + 1)
        [thm] sorted: idx + 4 < len → lookup heap (slot s (idx + 4)) ≤ lookup heap (next (slot s (idx + 4)))
        [thm] inj: idx + 5 ≠ idx + 4 → slot s (idx + 5) ≠ slot s (idx + 4)
        [thm] inj: idx ≠ idx + 4 → slot s idx ≠ slot s (idx + 4)
        [thm] next_def: next (slot s (idx + 4)) = slot s (idx + 4 + 1)
        [thm] inj: idx + 4 ≠ idx → slot s (idx + 4) ≠ slot s idx
        [thm] inj: idx + 1 ≠ idx + 4 → slot s (idx + 1) ≠ slot s (idx + 4)
        [thm] inj: idx + 4 ≠ idx + 3 → slot s (idx + 4) ≠ slot s (idx + 3)
        [thm] inj: idx + 7 ≠ idx + 4 → slot s (idx + 7) ≠ slot s (idx + 4)
        [thm] inj: idx + 4 ≠ idx + 5 → slot s (idx + 4) ≠ slot s (idx + 5)
        [thm] inj: idx + 2 ≠ idx + 4 → slot s (idx + 2) ≠ slot s (idx + 4)
        [thm] inj: idx + 4 ≠ idx + 7 → slot s (idx + 4) ≠ slot s (idx + 7)
        [thm] inj: idx + 6 ≠ idx + 4 → slot s (idx + 6) ≠ slot s (idx + 4)
        [thm] inj: idx + 4 ≠ idx + 6 → slot s (idx + 4) ≠ slot s (idx + 6)
        [thm] inj: idx + 3 ≠ idx + 4 → slot s (idx + 3) ≠ slot s (idx + 4)
        [thm] inj: idx + 4 ≠ idx + 2 → slot s (idx + 4) ≠ slot s (idx + 2)
      [thm] next_def: next (slot s (idx + 4)) = slot s (idx + 4 + 1) has 16 direct follow up instances
        [thm] inj: idx + 2 ≠ idx + 5 → slot s (idx + 2) ≠ slot s (idx + 5)
        [thm] inj: idx + 3 ≠ idx + 5 → slot s (idx + 3) ≠ slot s (idx + 5)
        [thm] inj: idx + 5 ≠ idx + 4 → slot s (idx + 5) ≠ slot s (idx + 4)
        [thm] inj: idx + 7 ≠ idx + 5 → slot s (idx + 7) ≠ slot s (idx + 5)
        [thm] inj: idx + 5 ≠ idx + 1 → slot s (idx + 5) ≠ slot s (idx + 1)
        [thm] inj: idx + 1 ≠ idx + 5 → slot s (idx + 1) ≠ slot s (idx + 5)
        [thm] inj: idx + 5 ≠ idx + 7 → slot s (idx + 5) ≠ slot s (idx + 7)
        [thm] inj: idx + 5 ≠ idx + 6 → slot s (idx + 5) ≠ slot s (idx + 6)
        [thm] next_def: next (slot s (idx + 5)) = slot s (idx + 5 + 1)
        [thm] inj: idx + 4 ≠ idx + 5 → slot s (idx + 4) ≠ slot s (idx + 5)
        [thm] inj: idx + 5 ≠ idx + 3 → slot s (idx + 5) ≠ slot s (idx + 3)
        [thm] inj: idx + 5 ≠ idx + 2 → slot s (idx + 5) ≠ slot s (idx + 2)
        [thm] inj: idx ≠ idx + 5 → slot s idx ≠ slot s (idx + 5)
        [thm] sorted: idx + 5 < len → lookup heap (slot s (idx + 5)) ≤ lookup heap (next (slot s (idx + 5)))
        [thm] inj: idx + 5 ≠ idx → slot s (idx + 5) ≠ slot s idx
        [thm] inj: idx + 6 ≠ idx + 5 → slot s (idx + 6) ≠ slot s (idx + 5)
      [thm] next_def: next (slot s (idx + 5)) = slot s (idx + 5 + 1) has 16 direct follow up instances
        [thm] inj: idx + 7 ≠ idx + 6 → slot s (idx + 7) ≠ slot s (idx + 6)
        [thm] inj: idx + 6 ≠ idx + 2 → slot s (idx + 6) ≠ slot s (idx + 2)
        [thm] inj: idx + 6 ≠ idx + 7 → slot s (idx + 6) ≠ slot s (idx + 7)
        [thm] inj: idx + 6 ≠ idx + 1 → slot s (idx + 6) ≠ slot s (idx + 1)
        [thm] inj: idx ≠ idx + 6 → slot s idx ≠ slot s (idx + 6)
        [thm] inj: idx + 2 ≠ idx + 6 → slot s (idx + 2) ≠ slot s (idx + 6)
        [thm] sorted: idx + 6 < len → lookup heap (slot s (idx + 6)) ≤ lookup heap (next (slot s (idx + 6)))
        [thm] inj: idx + 6 ≠ idx → slot s (idx + 6) ≠ slot s idx
        [thm] next_def: next (slot s (idx + 6)) = slot s (idx + 6 + 1)
        [thm] inj: idx + 5 ≠ idx + 6 → slot s (idx + 5) ≠ slot s (idx + 6)
        [thm] inj: idx + 3 ≠ idx + 6 → slot s (idx + 3) ≠ slot s (idx + 6)
        [thm] inj: idx + 6 ≠ idx + 4 → slot s (idx + 6) ≠ slot s (idx + 4)
        [thm] inj: idx + 6 ≠ idx + 3 → slot s (idx + 6) ≠ slot s (idx + 3)
        [thm] inj: idx + 1 ≠ idx + 6 → slot s (idx + 1) ≠ slot s (idx + 6)
        [thm] inj: idx + 4 ≠ idx + 6 → slot s (idx + 4) ≠ slot s (idx + 6)
        [thm] inj: idx + 6 ≠ idx + 5 → slot s (idx + 6) ≠ slot s (idx + 5)
      [thm] next_def: next (slot s (idx + 6)) = slot s (idx + 6 + 1) has 16 direct follow up instances
        [thm] inj: idx + 2 ≠ idx + 7 → slot s (idx + 2) ≠ slot s (idx + 7)
        [thm] inj: idx + 7 ≠ idx + 6 → slot s (idx + 7) ≠ slot s (idx + 6)
        [thm] inj: idx ≠ idx + 7 → slot s idx ≠ slot s (idx + 7)
        [thm] inj: idx + 7 ≠ idx + 5 → slot s (idx + 7) ≠ slot s (idx + 5)
        [thm] inj: idx + 1 ≠ idx + 7 → slot s (idx + 1) ≠ slot s (idx + 7)
        [thm] inj: idx + 6 ≠ idx + 7 → slot s (idx + 6) ≠ slot s (idx + 7)
        [thm] next_def: next (slot s (idx + 7)) = slot s (idx + 7 + 1)
        [thm] inj: idx + 5 ≠ idx + 7 → slot s (idx + 5) ≠ slot s (idx + 7)
        [thm] inj: idx + 7 ≠ idx + 4 → slot s (idx + 7) ≠ slot s (idx + 4)
        [thm] inj: idx + 7 ≠ idx → slot s (idx + 7) ≠ slot s idx
        [thm] inj: idx + 4 ≠ idx + 7 → slot s (idx + 4) ≠ slot s (idx + 7)
        [thm] inj: idx + 7 ≠ idx + 2 → slot s (idx + 7) ≠ slot s (idx + 2)
        [thm] inj: idx + 7 ≠ idx + 3 → slot s (idx + 7) ≠ slot s (idx + 3)
        [thm] sorted: idx + 7 < len → lookup heap (slot s (idx + 7)) ≤ lookup heap (next (slot s (idx + 7)))
        [thm] inj: idx + 7 ≠ idx + 1 → slot s (idx + 7) ≠ slot s (idx + 1)
        [thm] inj: idx + 3 ≠ idx + 7 → slot s (idx + 3) ≠ slot s (idx + 7)
      [thm] next_def: next (slot s idx) = slot s (idx + 1) has 15 direct follow up instances
        [thm] inj: idx + 4 ≠ idx + 1 → slot s (idx + 4) ≠ slot s (idx + 1)
        [thm] inj: idx + 1 ≠ idx + 7 → slot s (idx + 1) ≠ slot s (idx + 7)
        [thm] inj: idx + 1 ≠ idx + 2 → slot s (idx + 1) ≠ slot s (idx + 2)
        [thm] inj: idx + 5 ≠ idx + 1 → slot s (idx + 5) ≠ slot s (idx + 1)
        [thm] inj: idx + 6 ≠ idx + 1 → slot s (idx + 6) ≠ slot s (idx + 1)
        [thm] inj: idx + 1 ≠ idx + 4 → slot s (idx + 1) ≠ slot s (idx + 4)
        [thm] inj: idx + 1 ≠ idx + 5 → slot s (idx + 1) ≠ slot s (idx + 5)
        [thm] inj: idx + 1 ≠ idx + 3 → slot s (idx + 1) ≠ slot s (idx + 3)
        [thm] next_def: next (slot s (idx + 1)) = slot s (idx + 1 + 1)
        [thm] inj: idx ≠ idx + 1 → slot s idx ≠ slot s (idx + 1)
        [thm] inj: idx + 2 ≠ idx + 1 → slot s (idx + 2) ≠ slot s (idx + 1)
        [thm] inj: idx + 3 ≠ idx + 1 → slot s (idx + 3) ≠ slot s (idx + 1)
        [thm] inj: idx + 1 ≠ idx + 6 → slot s (idx + 1) ≠ slot s (idx + 6)
        [thm] inj: idx + 1 ≠ idx → slot s (idx + 1) ≠ slot s idx
        [thm] inj: idx + 7 ≠ idx + 1 → slot s (idx + 7) ≠ slot s (idx + 1)
-/
#guard_msgs in
set_option grind.ematch.diagnostics true in
example (h1 : idx < len) :
    -- Actually false, but this is a slow failure
    lookup heap (slot s idx) < lookup heap (next (slot s idx)) := by
  grind
