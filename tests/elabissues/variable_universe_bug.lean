/-
Courtesy of @rwbarton.

This is just a bug report, but since we are going to soon rewrite the entire module in Lean4,
we don't want to bother fixing the C++ bug, and we don't want to add a failing test either.

The issue is that collecting implicit locals does not collect additional universe parameters
the locals depend on.
-/
universes v u
class Category (C : Type u) :=
(Hom : ∀ (X Y : C), Type v)

variable {C : Type u} [Category.{v, u} C]

def End (X : C) := Category.Hom X X -- invalid reference to undefined universe level parameter 'v'
