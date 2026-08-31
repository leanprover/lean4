/-!
# Verify that the `noConfusion` lemma succeeds at being generated, despite the inductive type not being a syntactical telescope
Fixes https://github.com/leanprover/lean4/issues/2500
Ensures the `to_telescope` call in `mk_no_confusion_type` (`src/library/constructions/no_confusion.cpp`) takes the global environment into account,
thus allowing for delta-reduction.
-/

def family := Type → Type

inductive bad : family

def Set (A : Type _) := A → Prop

inductive Thing (s : Set V) : Set V
| basic : ∀ x, s x → Thing s x
