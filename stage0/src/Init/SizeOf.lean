prelude
import Init.Core

universes u v w

/- sizeof -/

class SizeOf (α : Sort u) :=
  (sizeOf : α → Nat)

export SizeOf (sizeOf)

/-
Declare sizeOf instances and theorems for types declared before SizeOf.
From now on, the inductive Compiler will automatically generate sizeOf instances and theorems.
-/

/- Every Type `α` has a default SizeOf instance that just returns 0 for every element of `α` -/
protected def default.sizeOf (α : Sort u) : α → Nat
  | a => 0

instance (α : Sort u) : SizeOf α :=
  ⟨default.sizeOf α⟩

instance : SizeOf Nat := {
  sizeOf := fun n => n
}

instance (α : Type u) (β : Type v) [SizeOf α] [SizeOf β] : SizeOf (Prod α β) := {
  sizeOf := fun (a, b) => 1 + sizeOf a + sizeOf b
}

instance (α : Type u) (β : Type v) [SizeOf α] [SizeOf β] : SizeOf (Sum α β) := {
  sizeOf := fun
    | Sum.inl a => 1 + sizeOf a
    | Sum.inr b => 1 + sizeOf b
}

instance (α : Type u) (β : Type v) [SizeOf α] [SizeOf β] : SizeOf (PSum α β) := {
  sizeOf := fun
    | PSum.inl a => 1 + sizeOf a
    | PSum.inr b => 1 + sizeOf b
}

instance (α : Type u) (β : α → Type v) [SizeOf α] [∀ a, SizeOf (β a)] : SizeOf (Sigma β) := {
  sizeOf := fun ⟨a, b⟩ => 1 + sizeOf a + sizeOf b
}

instance (α : Type u) (β : α → Type v) [SizeOf α] [(a : α) → SizeOf (β a)] : SizeOf (PSigma β) := {
  sizeOf := fun ⟨a, b⟩ => 1 + sizeOf a + sizeOf b
}

instance : SizeOf PUnit := {
  sizeOf := fun _ => 1
}

instance : SizeOf Bool := {
  sizeOf := fun _ => 1
}

instance (α : Type u) [SizeOf α] : SizeOf (Option α) := {
  sizeOf := fun
    | none   => 1
    | some a => 1 + sizeOf a
}

instance (α : Type u) [SizeOf α] : SizeOf (List α) := {
  sizeOf := fun as =>
    let rec loop
      | List.nil      => 1
      | List.cons x xs => 1 + sizeOf x + loop xs
    loop as
}

instance {α : Type u} [SizeOf α] (p : α → Prop) : SizeOf (Subtype p) := {
  sizeOf := fun ⟨a, _⟩ => sizeOf a
}
