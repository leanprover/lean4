import Std

set_option trace.Meta.Tactic.bv.epr true in
example {α : Type u} (a b : α) (h1 : a ≠ b) (h2 : ∀ (x y : α), x = y) {β : Type 1}
    (p : α → β → Prop) (c : β) (h : p a c): False := by
  bv_decide +epr




theorem foo {α : Type} (a b c : α) (p : α → Prop) (h1 : a = b → b = c) (h2 : a = b) (h3 : p a ≠ p c) : False := by
  bv_decide +epr +uf

theorem exp {α : Type} (a b : α) (h1 : ∀ (x y : α), x = y) (h2 : a ≠ b) : False := by
  bv_decide +epr +uf

theorem bar {α : Type} (a b : α) (p : α → Prop) (h1 : ∀ (x y : α), x = y) (h2 : p a ≠ p b) : False := by
  bv_decide +epr +uf

set_option trace.Meta.Tactic.bv true in
set_option trace.Meta.Tactic.bv.epr true in
theorem foobar {α : Type} (a b : α) (p : α → Prop) (h1 : ∀ (x y : α), p x = p y) (h2 : p a ≠ p b) : False := by
  bv_decide +epr +uf

set_option trace.profiler true in
theorem foobar' {α : Type} (a b : α) (p : α → Prop) (h1 : ∀ (x y : α), p x = p a) (h2 : p a ≠ p b) : False := by
  bv_decide +epr +uf




theorem card {α : Type} (a b c d : α) (p : α → Prop) (h1 : ∀ (x : α), x = a ∨ x = b) (h5 : p b ≠ p c) : False := by
  bv_decide +epr +uf
