/-! Verify that the derive handler for `DecidableEq` handles mutual inductive types-/

-- Print the generated derivations
set_option trace.Elab.Deriving.decEq true
set_option trace.Elab.Deriving true

mutual
inductive Tree :=
  | node : ListTree → Tree

inductive ListTree :=
  | nil : ListTree
  | cons : Tree → ListTree → ListTree
  deriving DecidableEq
end

inductive Tree' (α : Type _) : Type  _:=
  | node : α → Option (List (Tree' α)) → Tree' α
deriving DecidableEq

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

inductive Min' where
  | Base
  | Const (a : List Min')
deriving DecidableEq

inductive ComplexInductive (A B C : Type) (n : Nat) : Type
  | constr : A → B → C → ComplexInductive A B C n

inductive NestedComplex (A C : Type) : Type
  | constr : ComplexInductive A (NestedComplex A C) C 1 → NestedComplex A C
deriving DecidableEq
