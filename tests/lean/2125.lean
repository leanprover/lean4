open Classical

noncomputable def f (α : Type) : Bool :=
  Nonempty α

-- The following inductive is unsound:
inductive C : Bool → Type
  -- Must be rejected because `C` occurs inside an index.
  | c : C (f (C false))
