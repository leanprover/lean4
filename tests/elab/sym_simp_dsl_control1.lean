/-! Tests for `control` and `arrow_telescope` simproc DSL primitives.
Based on `sym_simp_4.lean` but using `register_sym_simp` + DSL instead of custom Lean tactics. -/

register_sym_simp mySimp where
  pre  := control >> arrow_telescope
  post := ground >> rewrite [and_true] with self

example : (if true then a else b) = a := by
  sym => simp mySimp

example : (if True then a else b) = a := by
  sym => simp mySimp

example : (if False then a else b) = b := by
  sym => simp mySimp

/--
trace: case grind
α✝ : Sort u_1
x : α✝
p q : Prop
h : p → q
⊢ p → q
-/
#guard_msgs in
example (p q : Prop) (h : p → q) : True → p → x = x → q := by
  sym =>
    simp mySimp
    show_goals
    exact h

example (p q : Prop) : q → p → True := by
  sym => simp mySimp

example (p q : Prop) : q → p → x = x := by
  sym => simp mySimp

example (q : Prop) : q → x ≠ x → True := by
  sym => simp mySimp

example (α : Type) (p : Prop) : α → p → x = x := by
  sym => simp mySimp

example (q : Prop) (α : Type) (p : Prop) : q → α → p → x = x := by
  sym => simp mySimp

example (α β : Type) (p q : Prop) : q → β → p → α → True := by
  sym => simp mySimp

/--
trace: case grind
α : Type u
x : α
p : Prop
h : α → p → True → α
⊢ α → p → True → α
-/
#guard_msgs in
example (α : Type u) (x : α) (p : Prop) (h : α → p → True → α) : α → p → x = x → α := by
  sym =>
    simp mySimp
    show_goals
    exact h

set_option linter.unusedVariables false

def F := False

/--
trace: case grind
α : Type
x : α
q : Prop
h : F
⊢ ∀ (a b : α), q
-/
#guard_msgs in
example (α : Type) (x : α) (q : Prop) (h : F) : (a : α) → x = x → (b : α) → True → q := by
  sym =>
    simp mySimp
    show_goals
    exact False.elim h

/--
trace: case grind
α : Sort u
x : α
p q : Prop
h : F
⊢ ∀ (a : α) {b : α}, q
-/
#guard_msgs in
example (α : Sort u) (x : α) (p q : Prop) (h : F) : (a : α) → x = x → {b : α} → True → (q ∧ True) := by
  sym =>
    simp mySimp
    show_goals
    exact False.elim h
