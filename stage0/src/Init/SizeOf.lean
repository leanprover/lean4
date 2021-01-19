prelude
import Init.Core

universes u v w

/- sizeof -/

class SizeOf (α : Sort u) where
  sizeOf : α → Nat

export SizeOf (sizeOf)

/-
Declare sizeOf instances and theorems for types declared before SizeOf.
From now on, the inductive Compiler will automatically generate sizeOf instances and theorems.
-/

/- Every Type `α` has a default SizeOf instance that just returns 0 for every element of `α` -/
protected def default.sizeOf (α : Sort u) : α → Nat
  | a => 0

instance (priority := low) (α : Sort u) : SizeOf α where
  sizeOf := default.sizeOf α

instance : SizeOf Nat where
  sizeOf n := n

instance (α : Type u) (β : Type v) [SizeOf α] [SizeOf β] : SizeOf (Prod α β) where
  sizeOf | (a, b) => 1 + sizeOf a + sizeOf b


instance (α : Type u) (β : Type v) [SizeOf α] [SizeOf β] : SizeOf (Sum α β) where
  sizeOf
    | Sum.inl a => 1 + sizeOf a
    | Sum.inr b => 1 + sizeOf b

instance (α : Type u) (β : Type v) [SizeOf α] [SizeOf β] : SizeOf (PSum α β) where
  sizeOf
    | PSum.inl a => 1 + sizeOf a
    | PSum.inr b => 1 + sizeOf b

instance (α : Type u) (β : α → Type v) [SizeOf α] [(a : α) → SizeOf (β a)] : SizeOf (Sigma β) where
  sizeOf | ⟨a, b⟩ => 1 + sizeOf a + sizeOf b

instance (α : Type u) (β : α → Type v) [SizeOf α] [(a : α) → SizeOf (β a)] : SizeOf (PSigma β) where
  sizeOf | ⟨a, b⟩ => 1 + sizeOf a + sizeOf b

instance : SizeOf PUnit where
  sizeOf _ := 1

instance : SizeOf Bool where
  sizeOf _ := 1

instance (α : Type u) [SizeOf α] : SizeOf (Option α) where
  sizeOf
    | none   => 1
    | some a => 1 + sizeOf a

protected def List.sizeOf [SizeOf α] : List α → Nat
  | []    => 1
  | x::xs => 1 + sizeOf x + List.sizeOf xs

instance (α : Type u) [SizeOf α] : SizeOf (List α) where
  sizeOf xs := xs.sizeOf

instance {α : Type u} [SizeOf α] (p : α → Prop) : SizeOf (Subtype p) where
  sizeOf | ⟨a, _⟩ => sizeOf a
