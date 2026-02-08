/-! Verify that the derive handler for `DecidableEq` handles mutual inductive types-/

-- Print the generated derivations
set_option trace.Elab.Deriving.decEq true

namespace A
set_option deriving.decEq.linear_construction_threshold 1000

mutual
inductive Tree : Type where
  | node : ListTree → Tree

inductive ListTree : Type where
  | nil : ListTree
  | cons : Tree → ListTree → ListTree
  deriving DecidableEq
end

mutual
inductive Foo₁ : Type where
  | foo₁₁ : Foo₁
  | foo₁₂ : Foo₂ → Foo₁
deriving DecidableEq

inductive Foo₂ : Type where
  | foo₂ : Foo₃ → Foo₂

inductive Foo₃ : Type where
  | foo₃ : Foo₁ → Foo₃
end

end A

namespace B
set_option deriving.decEq.linear_construction_threshold 0

mutual
inductive Tree : Type where
  | node : ListTree → Tree

inductive ListTree : Type where
  | nil : ListTree
  | cons : Tree → ListTree → ListTree
  deriving DecidableEq
end

mutual
inductive Foo₁ : Type where
  | foo₁₁ : Foo₁
  | foo₁₂ : Foo₂ → Foo₁
deriving DecidableEq

inductive Foo₂ : Type where
  | foo₂ : Foo₃ → Foo₂

inductive Foo₃ : Type where
  | foo₃ : Foo₁ → Foo₃
end

end B
