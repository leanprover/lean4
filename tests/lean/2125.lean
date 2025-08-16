open Classical

noncomputable def f (α : Type) : Bool :=
  Nonempty α

-- The following inductive is unsound:

inductive C : Bool → Type
  -- Must be rejected because `C` occurs inside an index.
  | c : C (f (C false))

-- Same, in arguments of the constructors

inductive D : Bool → Type
  -- Must be rejected because `D` occurs inside an index.
  | c : D (f (D false)) → D true

-- Same, but hidden behind nested induction

inductive Nest (G : Bool → Type) where
  | mk : G (f (G false)) → Nest G

inductive E : Bool → Type where
  -- Must be rejected because `D` occurs inside an index.
  | c : Nest E → E true
