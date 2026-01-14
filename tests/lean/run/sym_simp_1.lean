import Lean
open Lean Meta Elab Tactic

theorem bv0_eq (x : BitVec 0) : x = 0 := BitVec.of_length_zero

set_option warn.sorry false

elab "sym_simp" "[" declNames:ident,* "]" : tactic => do
  let declNames ← declNames.getElems.mapM resolveGlobalConstNoOverload
  liftMetaTactic1 <| Sym.simpGoal declNames

theorem heq_self : (x ≍ x) = True := by simp
theorem forall_true {α : Sort u} : (∀ _ : α, True) = True := by simp

example : x + 0 ≍ x := by
  fail_if_success sym_simp []
  sym_simp [Nat.add_zero, heq_self]

example : 0 + x + 0 = x := by
  sym_simp [Nat.add_zero, Nat.zero_add, eq_self]

example : x = x := by
  sym_simp [bv0_eq, eq_self]

example (x y : BitVec 0) : x = y := by
  sym_simp [bv0_eq, eq_self]

example : ∀ x, 0 + x + 0 = x := by
  sym_simp [Nat.add_zero, Nat.zero_add, eq_self]
  sym_simp [forall_true]

example : ∀ x, 0 + x + 0 = x := by
  sym_simp [Nat.add_zero, Nat.zero_add, eq_self, forall_true]

example (p q : Prop) (hp : p) : if x + 0 = x then p else q := by
  sym_simp [Nat.add_zero, eq_self, if_true]
  exact hp

example (as : Array Int) (i : Nat) (h : 0 + i < as.size) : as[0 + i] = as[i] := by
  sym_simp [Nat.zero_add, eq_self]

/-- trace: ⊢ Nat.add 0 = id -/
#guard_msgs in
example : Nat.add (0 + 0) = id := by
  sym_simp [Nat.zero_add]
  trace_state
  funext
  simp

/--
trace: a : Nat
β✝ : Type
f : β✝ → Prop
h : HEq a = f
⊢ HEq a = f
-/
#guard_msgs in
example (h : HEq a = f) : HEq (α := Nat) (0 + a) = f := by
  sym_simp [Nat.zero_add]
  trace_state
  exact h
