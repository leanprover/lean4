import Lean.Parser.Term

/-!
# Invalid projection error messages

This file assesses error messages produced for invalid projections.
-/

inductive P : Nat → n > 0 → Prop
  | mk (n) (q : n > 0) : P n q

/--
error: Invalid projection: Index `2` is invalid for this structure; the only valid index is 1

Note: The expression
  h2
has type `P m h'` which has only 1 field
-/
#guard_msgs in
example (h1 : P n h) (h2 : P m h') := h1.1 = h2.2

/--
error: Invalid projection: Projection operates on types of the form `C ...` where C is a constant. The expression
  Nat
has type `Type` which does not have the necessary form.
-/
#guard_msgs in
#check Nat.3

/--
error: Invalid projection: Index `3` is invalid for this structure; it must be between 1 and 2

Note: The expression
  x
has type `Nat × Nat × Nat` which has only 2 fields

Hint: n-tuples in Lean are actually nested pairs. To access the third component of this tuple, use the projection `.2.2` instead:
  3̵2̲.̲2̲
-/
#guard_msgs in
example (x : Nat × Nat × Nat) := x.3

/--
error: Invalid projection: Projection operates on structure-like types with fields. The expression
  h
has type `Nat` which does not have fields.
-/
#guard_msgs in
example (h : Nat) := h.2

/--
error: Invalid projection: Projections cannot be used on functions, and
  f
has function type `Nat → Nat`
-/
#guard_msgs in
example (f : Nat → Nat) := f.1

-- Currently, this error can only occur metaprogrammatically:
open Lean in
macro "bad_projection" : term =>
  return ⟨mkNode ``Parser.Term.proj
    #[mkIdent `h, mkAtom ".", mkNode fieldIdxKind #[mkAtom "0"]]⟩

/-- error: Invalid projection: Index must be greater than 0 -/
#guard_msgs in
example (h : Nat × Nat) := bad_projection

/-! ## Would-be unsound projections -/

-- Projection to the witness should be rejected.
/--
error: Invalid projection: Cannot project a value of non-propositional type
  Nat
from the expression
  Exists.intro 1 (Nat.le_refl 1)
which has propositional type
  ∃ x, x ≥ 1
-/
#guard_msgs in
def witness : Nat := (⟨1, Nat.le_refl _⟩ : ∃ x, x ≥ 1).1

-- Projection to the property as well (it could contain the witness projection).
/--
error: (kernel) invalid projection
  h.2
-/
#guard_msgs in
theorem witness_eq (h : ∃ x : Nat, True) : h.2 = h.2 := rfl

/--
error: Invalid projection: Cannot project a value of non-propositional type
  Nat
from the expression
  h
which has propositional type
  ∃ x, True
-/
#guard_msgs in
def foo (h : ∃ x: Nat, True) := h.1
