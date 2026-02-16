/-!
# Test that `lia` does not use the order module

The `lia` tactic is for linear integer arithmetic only.
It should not solve rational number inequalities that require the order module.
-/

-- This should fail: lia should not handle rational inequalities
/--
error: `grind` failed
case grind
k : Rat
hk : 2 ≤ k
h : ¬1 ≤ k
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] 2 ≤ k
    [prop] ¬1 ≤ k
  [eqc] True propositions
    [prop] 2 ≤ k
  [eqc] False propositions
    [prop] 1 ≤ k
  [limits] Thresholds reached
    [limit] maximum number of E-matching rounds has been reached, threshold: `(ematch := 0)`
-/
#guard_msgs in
example (k : Rat) (hk : 2 ≤ k) : 1 ≤ k := by lia

example (k : Rat) (hk : 2 ≤ k) : 1 ≤ k := by lia +order

example (k : Rat) (hk : 2 ≤ k) : 1 ≤ k := by grind_order

-- This should still work: natural number inequalities are handled by lia
example (k : Nat) (hk : 2 ≤ k) : 1 ≤ k := by lia

-- This should still work with explicit -order flag (no change in behavior)
example (k : Nat) (hk : 2 ≤ k) : 1 ≤ k := by lia -order
