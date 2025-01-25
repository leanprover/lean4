def g (i : Nat) (j : Nat) := i + j

set_option grind.debug true
set_option grind.debug.proofs true

/--
error: `grind` failed
case grind
i j : Nat
h : j + 1 ≤ i
x✝ : ¬g (i + 1) j = i + 1
⊢ False
[grind] Diagnostics
  [facts] Asserted facts
    [prop] j + 1 ≤ i
    [prop] ¬g (i + 1) j = i + 1
  [eqc] True propositions
    [prop] j + 1 ≤ i
  [eqc] False propositions
    [prop] g (i + 1) j = i + 1
  [offset] Assignment satisfying offset contraints
    [assign] j := 0
    [assign] i := 1
    [assign] i + 1 := 2
    [assign] 0 := 0
-/
#guard_msgs (error) in
example (i j : Nat) (h : i + 1 > j + 1) : g (i+1) j = i + 1 := by
  grind

/--
error: `grind` failed
case grind
i : Nat
x✝ : 101 ≤ i
⊢ False
[grind] Diagnostics
  [facts] Asserted facts
    [prop] 101 ≤ i
  [eqc] True propositions
    [prop] 101 ≤ i
  [offset] Assignment satisfying offset contraints
    [assign] 0 := 0
    [assign] i := 101
-/
#guard_msgs (error) in
example (i : Nat) : i ≤ 100 := by
  grind

/--
error: `grind` failed
case grind
i : Nat
x✝ : i ≤ 99
⊢ False
[grind] Diagnostics
  [facts] Asserted facts
    [prop] i ≤ 99
  [eqc] True propositions
    [prop] i ≤ 99
  [offset] Assignment satisfying offset contraints
    [assign] i := 99
    [assign] 0 := 0
-/
#guard_msgs (error) in
example (i : Nat) : 100 ≤ i := by
  grind

/--
error: `grind` failed
case grind
n m a j i : Nat
a✝ : g (n + 1) m = a
x✝ : i ≤ j + 99
⊢ False
[grind] Diagnostics
  [facts] Asserted facts
    [prop] g (n + 1) m = a
    [prop] i ≤ j + 99
  [eqc] True propositions
    [prop] i ≤ j + 99
  [eqc] Equivalence classes
    [eqc] {g (n + 1) m, a}
  [offset] Assignment satisfying offset contraints
    [assign] n + 1 := 1
    [assign] n := 0
    [assign] 0 := 0
    [assign] i := 99
    [assign] j := 0
-/
#guard_msgs (error) in
example (i : Nat) : g (n + 1) m = a → 100 + j ≤ i := by
  grind

/--
error: `grind` failed
case grind
n m a j i : Nat
a✝ : g (n + 1) m = a
x✝ : i + 101 ≤ j
⊢ False
[grind] Diagnostics
  [facts] Asserted facts
    [prop] g (n + 1) m = a
    [prop] i + 101 ≤ j
  [eqc] True propositions
    [prop] i + 101 ≤ j
  [eqc] Equivalence classes
    [eqc] {g (n + 1) m, a}
  [offset] Assignment satisfying offset contraints
    [assign] n + 1 := 1
    [assign] n := 0
    [assign] 0 := 0
    [assign] i := 0
    [assign] j := 101
-/
#guard_msgs (error) in
example (i : Nat) : g (n + 1) m = a → j ≤ i + 100 := by
  grind
