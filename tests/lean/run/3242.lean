mutual
inductive A (α : Type) : α → Type where

inductive B (α : Type) : α → Type where
end

mutual
inductive R (F: α → α → Prop) (a : α) : α → Prop where
  | ind : ∀ (f: Nat → α) b, (∀ n, And₂ F a b f n) → R F a b

inductive And₂ (F: α → α → Prop) (a : α) : α → (Nat → α) → Nat → Prop where
  | mk (b : α) (f : Nat → α) (n : Nat): R F a (f n) → F (f n) b → And₂ F a b f n
end

structure Salg (n k: Nat) where
  D: Type

mutual
inductive Ins (salg: Salg n k) : salg.D → Prop
inductive Out (salg: Salg n k) : salg.D → Prop
end
