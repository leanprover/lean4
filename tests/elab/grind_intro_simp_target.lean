/-!
`grind` normalizes the goal before negating it. An implication or universal quantifier exposed
by the normalizer is introduced like a syntactic one.

Regression test for Sebastian Graf's report after #15378: the `Imp` goal below was no longer
proved, while the same goal with a syntactic `→` still was.
-/

def Imp (a b : Prop) : Prop := a → b
@[grind norm] theorem Imp_eq (a b : Prop) : Imp a b = (a → b) := rfl

def All (p : Nat → Prop) : Prop := ∀ x, p x
@[grind norm] theorem All_eq (p : Nat → Prop) : All p = ∀ x, p x := rfl

/--
trace: [grind.assert] 4 ≤ n
[grind.assert] ∀ (i : Nat), i + 1 ≤ n → ∃ j, j = i + 1 ∧ p j
[grind.assert] ¬p 4
[grind.assert] 4 ≤ n → ∃ j, j = 4 ∧ p j
[grind.assert] w = 4
[grind.assert] p w
-/
#guard_msgs in
set_option trace.grind.assert true in
example (n : Nat) (p : Nat → Prop) (hn : 3 < n) :
    Imp (∀ i, i < n → ∃ j, j = i + 1 ∧ p j) (p 4) := by grind

example (n : Nat) (p : Nat → Prop) :
    Imp (3 < n) (Imp (∀ i, i < n → ∃ j, j = i + 1 ∧ p j) (p 4)) := by grind

example (n : Nat) (p : Nat → Prop) :
    3 < n → Imp (∀ i, i < n → ∃ j, j = i + 1 ∧ p j) (p 4) := by grind

example (n : Nat) (q : Nat → Prop) (h : ∀ i, q i) : All fun i => Imp (i < n) (q i) := by grind

example (n : Nat) (p : Nat → Prop) :
    All fun m => Imp (m = n) (Imp (3 < m) (Imp (∀ i, i < n → ∃ j, j = i + 1 ∧ p j) (p 4))) := by
  grind

example (p : Prop) : Imp p p := by grind
example (p q : Prop) : Imp p (Imp q p) := by grind
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by grind
example (a b : Nat) (h : a < b) : a ≤ b := by grind

-- The hypotheses are introduced one at a time, as in the syntactic case.
/--
error: `grind` failed
case grind
p q : Prop
h : p
h_1 : ¬q
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] p
    [prop] ¬q
  [eqc] True propositions
    [prop] p
  [eqc] False propositions
    [prop] q
-/
#guard_msgs in
example (p q : Prop) : Imp p q := by grind
