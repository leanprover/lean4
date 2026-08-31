/-!
# Tests of universe constraints for inductive types

https://github.com/leanprover/lean4/pull/2689 corrected the elaborator's `Level.geq`,
which was missing cases that the kernel `is_geq` could handle.
-/

/-!
This always worked. The universe level of `Trans₁` is inferred from the fields.
-/
structure Trans₁ {α : Sort a} {β : Sort b} {γ : Sort c}
    (r : α → β → Sort u) (s : β → γ → Sort v) (t : outParam (α → γ → Sort w)) where
  trans : r a b → s b c → t a c

/-!
Regression test: This was failing. An explicit universe invokes `Level.geq`.
-/
structure Trans₂ {α : Sort a} {β : Sort b} {γ : Sort c}
    (r : α → β → Sort u) (s : β → γ → Sort v) (t : outParam (α → γ → Sort w)) :
    Sort (max 1 a b c u v w) where
  trans : r a b → s b c → t a c

/-!
Regression test: This was failing. An explicit universe invokes `Level.geq`.
-/
inductive Trans₃ {α : Sort a} {β : Sort b} {γ : Sort c}
    (r : α → β → Sort u) (s : β → γ → Sort v) (t : outParam (α → γ → Sort w)) :
    Sort (max 1 a b c u v w) where
  | mk : (∀ a b c, r a b → s b c → t a c) → Trans₃ r s t

/-!
Regression test: This was failing due to the included `Type (max u v)`
even though this is the inferred universe.
-/
inductive I (α : Type u) (Hom : α → α → Sort v) : Type (max u v) where
  | mk (id : ∀ X : α, Hom X X)
