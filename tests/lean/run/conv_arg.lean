/-!
# Tests for `conv` mode `arg` tactic
-/

/-!
Basic `arg` usage
-/
example (a b : Nat) (h : b = a) : a + b = a + a := by
  conv =>
    enter [1, 2]
    rw [h]

example (a b : Nat) (h : b = a) : a + b = a + a := by
  conv =>
    enter [-2, -1]
    rw [h]

-- Implications
example (p₁ p₂ q : Prop) (h : p₁ ↔ p₂) : (p₁ → q) ↔ (p₂ → q) := by
  conv => enter [1, 1]
  conv =>
    enter [1, 1]
    rw [h]

example (p q₁ q₂ : Prop) (h : q₁ ↔ q₂) : (p → q₁) ↔ (p → q₂) := by
  conv => enter [1, 2]
  conv =>
    enter [1, 2]
    rw [h]

-- Dependent implications
/--
info: i✝ : Nat
| i✝ < 10
---
info: a✝¹ : Nat
a✝ : a✝¹ < 10
| ↑⟨a✝¹, ⋯⟩ = a✝¹
-/
#guard_msgs in
example : ∀ (i : Nat) (h : i < 10), (⟨i, h⟩ : Fin 10).val = i := by
  conv =>
    enter [2,1]
    trace_state
  conv =>
    enter [2,2]
    trace_state
    simp
  simp

/-!
Explicit mode
-/
example (f : {_ : Nat} → Nat → Nat) (h : n = n') : @f n m = @f n' m := by
  conv =>
    enter [1, @1]
    rw [h]

example (f : {_ : Nat} → Nat → Nat) (h : m = m') : @f n m = @f n m' := by
  conv =>
    enter [1, @2]
    rw [h]

/-!
Out of bounds errors.
-/

/--
error: invalid 'arg' tactic, application has 1 explicit argument(s) but the index is out of bounds
-/
#guard_msgs in
example (f : {_ : Nat} → Nat → Nat) (h : m = m') : @f n m = @f n m' := by
  conv =>
    enter [1, 6]

/-- error: invalid 'arg' tactic, application has 2 argument(s) but the index is out of bounds -/
#guard_msgs in
example (f : {_ : Nat} → Nat → Nat) (h : m = m') : @f n m = @f n m' := by
  conv =>
    enter [1, @6]

/-!
Issue https://github.com/leanprover/lean4/issues/5871
The `arg` tactic was `congr` theorems, which was too restrictive.
-/
class DFunLike (F : Sort _) (α : outParam (Sort _)) (β : outParam <| α → Sort _) where
  /-- The coercion from `F` to a function. -/
  coe : F → ∀ a : α, β a

structure MyFun (α β : Type) where
  toFun : α → β

instance : DFunLike (MyFun α β) α (fun _ => β) where
  coe f := f.toFun

example (a b : Nat) (h : a = b) (f : MyFun Nat Int) : DFunLike.coe f a = DFunLike.coe f b := by
  conv =>
    enter [1, 2] -- the `arg 2` used to fail
    rw [h]
