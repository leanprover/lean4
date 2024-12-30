import Lean

open Lean Meta Elab Tactic Grind in
elab "grind_pre" : tactic => do
  let declName := (← Term.getDeclName?).getD `_main
  liftMetaTactic fun mvarId => do
    Meta.Grind.main mvarId declName

abbrev f (a : α) := a

/--
info: a b c : Bool
p q : Prop
left✝ : a = true
right✝ : b = true ∨ c = true
left : p
right : q
x✝ : b = false ∨ a = false
⊢ False
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
theorem ex (h : (f a && (b || f (f c))) = true) (h' : p ∧ q) : b && a := by
  grind_pre
  trace_state
  all_goals sorry

open Lean.Grind.Eager in
/--
info: a b c : Bool
p q : Prop
left✝ : a = true
h✝ : b = true
left : p
right : q
h : b = false
⊢ False

a b c : Bool
p q : Prop
left✝ : a = true
h✝ : b = true
left : p
right : q
h : a = false
⊢ False

a b c : Bool
p q : Prop
left✝ : a = true
h✝ : c = true
left : p
right : q
h : b = false
⊢ False

a b c : Bool
p q : Prop
left✝ : a = true
h✝ : c = true
left : p
right : q
h : a = false
⊢ False
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
theorem ex2 (h : (f a && (b || f (f c))) = true) (h' : p ∧ q) : b && a := by
  grind_pre
  trace_state
  all_goals sorry


def g (i : Nat) (j : Nat) (_ : i > j := by omega) := i + j

example (i j : Nat) (h : i + 1 > j + 1) : g (i+1) j = f ((fun x => x) i) + f j + 1 := by
  grind_pre
  guard_hyp h : j + 1 ≤ i
  next hn =>
  guard_hyp hn : ¬g (i + 1) j _ = i + j + 1
  simp_arith [g] at hn

structure Point where
  x : Nat
  y : Int

/--
info: a₁ : Point
a₂ : Nat
a₃ : Int
as : List Point
b₁ : Point
bs : List Point
b₂ : Nat
b₃ : Int
head_eq : a₁ = b₁
x_eq : a₂ = b₂
y_eq : a₃ = b₃
tail_eq : as = bs
⊢ False
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
theorem ex3 (h : a₁ :: { x := a₂, y := a₃ : Point } :: as = b₁ :: { x := b₂, y := b₃} :: bs) : False := by
  grind_pre
  trace_state
  sorry
