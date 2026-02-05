import Lean
open Lean Meta Elab Tactic

elab "sym_simp" "[" declNames:ident,* "]" : tactic => do
  let rewrite ← Sym.mkSimprocFor (← declNames.getElems.mapM fun s => realizeGlobalConstNoOverload s.raw) Sym.Simp.dischargeSimpSelf
  let methods : Sym.Simp.Methods := {
    pre  := Sym.Simp.simpControl.andThen Sym.Simp.simpArrowTelescope
    post := Sym.Simp.evalGround.andThen rewrite
  }
  liftMetaTactic1 fun mvarId => Sym.SymM.run do
    let mvarId ← Sym.preprocessMVar mvarId
    (← Sym.simpGoal mvarId methods).toOption

example : (if true then a else b) = a := by
  sym_simp []

example : (if True then a else b) = a := by
  sym_simp []

example : (if False then a else b) = b := by
  sym_simp []

/--
trace: α✝ : Sort u_1
x : α✝
p q : Prop
h : p → q
⊢ p → q
-/
#guard_msgs in
example (p q : Prop) (h : p → q) : True → p → x = x → q := by
  sym_simp []
  trace_state
  exact h

example (p q : Prop) : q → p → True := by
  sym_simp []

example (p q : Prop) : q → p → x = x := by
  sym_simp []

example (q : Prop) : q → x ≠ x → True := by
  sym_simp []

example (α : Type) (p : Prop) : α → p → x = x := by
  sym_simp []

example (q : Prop) (α : Type) (p : Prop) : q → α → p → x = x := by
  sym_simp []

example (α β : Type) (p q : Prop) : q → β → p → α → True := by
  sym_simp []

/--
trace: α : Type u
x : α
p : Prop
h : α → p → True → α
⊢ α → p → True → α
-/
#guard_msgs in
example (α : Type u) (x : α) (p : Prop) (h : α → p → True → α) : α → p → x = x → α := by
  sym_simp []
  trace_state
  exact h

set_option linter.unusedVariables false

/--
trace: α : Type
x : α
q : Prop
h : False
⊢ ∀ (a b : α), q
-/
#guard_msgs in
example (α : Type) (x : α) (q : Prop) (h : False) : (a : α) → x = x → (b : α) → True → q := by
  sym_simp []
  trace_state
  cases h

/--
trace: α : Sort u
x : α
p q : Prop
h : False
⊢ ∀ (a : α) {b : α}, q
-/
#guard_msgs in
example (α : Sort u) (x : α) (p q : Prop) (h : False) : (a : α) → x = x → {b : α} → True → (q ∧ True) := by
  sym_simp [and_true]
  trace_state
  cases h
