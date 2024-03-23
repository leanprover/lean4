/-!
# Ensure that inductive types/structures whose fields all live in `Prop` also live in `Prop`
-/

inductive Foo₁ (α : Type _) where
  | foo : (∀ a : α, a = a) → Foo₁ α

#check Foo₁

structure Foo₂ (α : Type _) where
  h : ∀ a : α, a = a

#check Foo₂

