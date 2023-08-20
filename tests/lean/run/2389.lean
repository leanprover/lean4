/-!
# Verify that nested predicates don't trigger the generation of `below` lemmas
Since the case of nested predicates is not currently handled by `mkBelow` (in `src/Lean/Meta/IndPredBelow.lean`),
trying to generate `OnlyZeros.below` triggers an error upon defining the inductive type.
-/

inductive Forall (P : α → Prop) : List α → Prop
  | nil : Forall P []
  | cons : {x : α} → P x → Forall P l → Forall P (x::l)

inductive Tree : Type :=
  | leaf : Nat → Tree
  | node : List Tree → Tree

set_option trace.Meta.IndPredBelow true in

/-- Despite not having `.below` and `.brecOn`,
the type is still usable thanks to well-founded recursion. -/
inductive OnlyZeros : Tree → Prop :=
  | leaf : OnlyZeros (.leaf 0)
  | node (l : List Tree): Forall OnlyZeros l → OnlyZeros (.node l)

/-- Equivalent definition of `OnlyZeros`, defined by a function instead of an inductive type. -/
def onlyZeros : Tree → Prop
  | .leaf n => n = 0
  | .node [] => True
  | .node (x::s) => onlyZeros x ∧ onlyZeros (.node s)

/-- Pattern-matching on `OnlyZeros` works despite `below` and `brecOn` not being generated. -/
def toFixPoint : OnlyZeros t → onlyZeros t
  | .leaf => rfl
  | .node [] _ => True.intro
  | .node (x::s) (.cons h p) => by
    rw [onlyZeros] -- necessary because `onlyZeros` isn't structurally recursive
    exact And.intro (toFixPoint h) (toFixPoint (.node s p))
