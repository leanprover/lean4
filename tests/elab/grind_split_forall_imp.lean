/-!
`grind` case-splits on an implication whose antecedent is a universal quantifier, and the
normalizer keeps the implication. The normal form of a negated implication does not depend on
whether the implication is syntactic or exposed by a normalization rule.
-/

def Imp (a b : Prop) : Prop := a → b
@[grind norm] theorem Imp_eq (a b : Prop) : Imp a b = (a → b) := rfl

example (n : Nat) (p : Nat → Prop) (hn : 3 < n) :
    (∀ i, i < n → ∃ j, j = i + 1 ∧ p j) → p 4 := by grind

example (n : Nat) (p : Nat → Prop) (hn : 3 < n) :
    Imp (∀ i, i < n → ∃ j, j = i + 1 ∧ p j) (p 4) := by grind

example (n : Nat) (p : Nat → Prop) (a : Prop) (ha : a) (hn : 3 < n) :
    a ∧ Imp (∀ i, i < n → ∃ j, j = i + 1 ∧ p j) (p 4) := by grind

example (n : Nat) (p : Nat → Prop) (hn : 3 < n)
    (h : ¬ Imp (∀ i, i < n → ∃ j, j = i + 1 ∧ p j) (p 4)) : False := by grind

example (n : Nat) (p : Nat → Prop) (hn : 3 < n)
    (h : ((∀ i, i < n → ∃ j, j = i + 1 ∧ p j) → p 4) = False) : False := by grind

example (n : Nat) (q : Nat → Prop) (r : Prop) :
    (¬ Imp (∀ i, i < n → q i) r) = (¬ ((∀ i, i < n → q i) → r)) := by
  grind_norm
  exact True.intro

/--
trace: n : Nat
q : Nat → Prop
r : Prop
h : (∀ (i : Nat), i < n → q i) → r
⊢ (∀ (i : Nat), i + 1 ≤ n → q i) → r
-/
#guard_msgs in
example (n : Nat) (q : Nat → Prop) (r : Prop) (h : (∀ i, i < n → q i) → r) :
    (∀ i, i < n → q i) → r := by
  grind_norm
  trace_state
  exact h

-- The implication is a hypothesis, and its antecedent is not known to be true or false.
example (p : Nat → Prop) (q : Prop) (h₁ : (∀ x, p x) → q) (h₂ : (∃ x, ¬ p x) → q) : q := by
  grind

example (p : Nat → Prop) (q r : Prop) (h₁ : r ∨ ((∀ x, p x) → q)) (h₂ : (∃ x, ¬ p x) → q)
    (h₃ : ¬ r) : q := by
  grind

-- Induction hypotheses
theorem countP_mono {α} {P Q : α → Bool} {l : List α} (hpq : ∀ x ∈ l, P x → Q x) :
    l.countP P ≤ l.countP Q := by
  induction l <;> grind

-- The antecedent and the conclusion are not assigned by propagation: the proof needs the split.
/--
trace: [grind.split] ∀ (x : Nat), p x, generation: 0
-/
#guard_msgs in
set_option trace.grind.split true in
example (p : Nat → Prop) (f : Nat → Nat) (a : Nat)
    (h₁ : (∀ x, p x) → f a = 1) (h₂ : ∀ x, ¬ p x → f a = 2) :
    f (f a) = f 1 ∨ f (f a) = f 2 := by
  grind
