import Lean

/-!
The `grind` normalizer distributes a universal quantifier over a conjunction at the end of an
arrow telescope, `∀ x, p x → q x ∧ r x`, but keeps a non-dependent `p → a ∧ b`: `grind` obtains
`a ∧ b` from `p` by propagation, so splitting it only duplicates the antecedent.
-/

open Lean Elab Tactic in
elab "show_target" : tactic => withMainContext do logInfo m!"{← getMainTarget}"
macro "nf" : tactic => `(tactic| (grind_norm; show_target; sorry))
macro "nf_sym" : tactic => `(tactic| (grind_norm sym; show_target; sorry))

variable (a b : Prop) (p q r : Nat → Prop) (s : Nat → Nat → Prop)

/-- info: a → q 0 ∧ r 0 -/
#guard_msgs (info, drop warning) in
example : a → q 0 ∧ r 0 := by nf

/-- info: a → q 0 ∧ r 0 -/
#guard_msgs (info, drop warning) in
example : a → q 0 ∧ r 0 := by nf_sym

/-- info: (∀ (x : Nat), q x) ∧ ∀ (x : Nat), r x -/
#guard_msgs (info, drop warning) in
example : ∀ x, q x ∧ r x := by nf

/-- info: (∀ (x : Nat), q x) ∧ ∀ (x : Nat), r x -/
#guard_msgs (info, drop warning) in
example : ∀ x, q x ∧ r x := by nf_sym

/-- info: (∀ (x : Nat), p x → q x) ∧ ∀ (x : Nat), p x → r x -/
#guard_msgs (info, drop warning) in
example : ∀ x, p x → q x ∧ r x := by nf

/-- info: (∀ (x : Nat), p x → q x) ∧ ∀ (x : Nat), p x → r x -/
#guard_msgs (info, drop warning) in
example : ∀ x, p x → q x ∧ r x := by nf_sym

/-- info: (∀ (x : Nat), p x → a → q x) ∧ ∀ (x : Nat), p x → a → r x -/
#guard_msgs (info, drop warning) in
example : ∀ x, p x → a → q x ∧ r x := by nf

/-- info: (∀ (x : Nat), p x → a → q x) ∧ ∀ (x : Nat), p x → a → r x -/
#guard_msgs (info, drop warning) in
example : ∀ x, p x → a → q x ∧ r x := by nf_sym

/-- info: (∀ (x y : Nat), s x y → q x) ∧ ∀ (x y : Nat), s x y → r y -/
#guard_msgs (info, drop warning) in
example : ∀ x y, s x y → q x ∧ r y := by nf

/-- info: (∀ (x y : Nat), s x y → q x) ∧ ∀ (x y : Nat), s x y → r y -/
#guard_msgs (info, drop warning) in
example : ∀ x y, s x y → q x ∧ r y := by nf_sym

-- A non-dependent domain that is not a proposition is an arrow too.
/-- info: (∀ (x a : Nat), q x) ∧ ∀ (x a : Nat), r x -/
#guard_msgs (info, drop warning) in
example : ∀ x, Nat → q x ∧ r x := by nf

/-- info: (∀ (x a : Nat), q x) ∧ ∀ (x a : Nat), r x -/
#guard_msgs (info, drop warning) in
example : ∀ x, Nat → q x ∧ r x := by nf_sym

-- The split is what gives each conjunct its own E-matching pattern.
example (h : ∀ x, p x → q x ∧ r x) (h' : p 5) : r 5 := by grind
example (h : ∀ x y, s x y → q x ∧ r y) (h' : s 2 3) : q 2 ∧ r 3 := by grind

-- Nested telescopes and a quantifier below an arrow.
/-- info: (∀ (x : Nat), a → ∀ (y : Nat), s x y → q x) ∧ ∀ (x : Nat), a → ∀ (y : Nat), s x y → r y -/
#guard_msgs (info, drop warning) in
example : ∀ x, a → ∀ y, s x y → q x ∧ r y := by nf

/-- info: (∀ (x : Nat), a → ∀ (y : Nat), s x y → q x) ∧ ∀ (x : Nat), a → ∀ (y : Nat), s x y → r y -/
#guard_msgs (info, drop warning) in
example : ∀ x, a → ∀ y, s x y → q x ∧ r y := by nf_sym

/-- info: a → (∀ (y : Nat), q y) ∧ ∀ (y : Nat), r y -/
#guard_msgs (info, drop warning) in
example : a → ∀ y, q y ∧ r y := by nf

/-- info: a → (∀ (y : Nat), q y) ∧ ∀ (y : Nat), r y -/
#guard_msgs (info, drop warning) in
example : a → ∀ y, q y ∧ r y := by nf_sym
