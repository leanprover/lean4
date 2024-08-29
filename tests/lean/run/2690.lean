/-!
# Ensure that inductive types/structures whose fields all live in `Prop` also live in `Prop`
-/

inductive Foo₁ (α : Type _) where
  | foo : (∀ a : α, a = a) → Foo₁ α

/-- info: Foo₁.{u_1} (α : Type u_1) : Type -/
#guard_msgs in
#check Foo₁

structure Foo₂ (α : Type _) where
  h : ∀ a : α, a = a

/-- info: Foo₂.{u_1} (α : Type u_1) : Prop -/
#guard_msgs in
#check Foo₂
