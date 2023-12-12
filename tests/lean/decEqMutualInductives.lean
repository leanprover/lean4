/-! Verify that the derive handler for `DecidableEq` handles mutual inductive types-/

-- Print the generated derivations
set_option trace.Elab.Deriving.decEq true

mutual
inductive Tree : Type :=
  | node : ListTree → Tree

inductive ListTree : Type :=
  | nil : ListTree
  | cons : Tree → ListTree → ListTree
  deriving DecidableEq
end

mutual
inductive Foo₁ : Type :=
  | foo₁₁ : Foo₁
  | foo₁₂ : Foo₂ → Foo₁
deriving DecidableEq

inductive Foo₂ : Type :=
  | foo₂ : Foo₃ → Foo₂

inductive Foo₃ : Type :=
  | foo₃ : Foo₁ → Foo₃
end
