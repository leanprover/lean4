prelude
import Init.RCases
import Init.Data.Iterators.Basic
import Std.Data.Iterators.Producers.Monadic.List

/-!
This file provides a way to restrict the type of an iterator to the iterator itself and its
plausible successors. The resulting type is called the iterator's lineage iterator type.

The main application of this type is that if the original iterator is finite (in a suitable sense),
then its lineage iterator type can be proved to have a `Finite` instance, enabling well-founded
recursion.
-/

namespace Std.Iterators

structure Lineage {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    (it : IterM (α := α) m β) where
  inner : IterM (α := α) m β
  is_transitive_successor : IterM.IsInLineageOf inner it

instance [Iterator α m β] [Monad m] (it : IterM (α := α) m β) :
    Iterator (Lineage it) m β where
  IsPlausibleStep it' step := it'.internalState.inner.IsPlausibleStep (step.mapIterator (·.internalState.inner))
  step it' := by
    refine (fun step => ⟨step.1.pmapIterator (fun it'' h => ⟨it'', ?_⟩), ?_⟩) <$> it'.internalState.inner.step
    · rcases step with ⟨step, hs⟩
      cases step <;> simp [hs]
    · refine IterM.IsInLineageOf.trans (it' := ?_) ?fst ?snd
      case snd => exact it'.internalState.is_transitive_successor
      case fst =>
      · apply IterM.IsInLineageOf.single
        exact ⟨step.1, h, step.2⟩

instance Lineage.instFiniteOfFinite [Iterator α m β] [h : Finite α m] [Monad m] (it : IterM (α := α) m β) :
    Finite (Lineage it) m := sorry

def IterM.IsFinite [Iterator α m β] [Monad m] (it : IterM (α := α) m β) :=
  Finite (Lineage it) m

def FiniteIterator [Iterator α m β] [Monad m] (it : IterM (α := α) m β)
    (_ : it.IsFinite) :=
  Lineage it

instance [Iterator α m β] [Monad m] (it : IterM (α := α) m β) (h : it.IsFinite) :
    Iterator (FiniteIterator it h) m β :=
  inferInstanceAs <| Iterator (Lineage it) m β

instance [Iterator α m β] [Monad m] (it : IterM (α := α) m β) (h : it.IsFinite) :
    Finite (FiniteIterator it h) m :=
  h

@[always_inline, inline]
def IterM.Advanced.lineage [Iterator α m β] (it : IterM (α := α) m β) :
    IterM (α := Lineage it) m β :=
  ⟨it, .rfl⟩

/--
`finite_iterator_tactic_trivial` is an extensible tactic automatically called
by the notation `arr[i]` to prove any side conditions that arise when
constructing the term (e.g. the index is in bounds of the array).
The default behavior is to just try `trivial` (which handles the case
where `i < arr.size` is in the context) and `simp +arith` and `omega`
(for doing linear arithmetic in the index).
-/
syntax "finite_iterator_tactic_trivial" : tactic

macro_rules | `(tactic| finite_iterator_tactic_trivial) => `(tactic| exact inferInstanceAs (Finite _ _))
-- macro_rules | `(tactic| finite_iterator_tactic_trivial) => `(tactic| simp +arith; done)
-- macro_rules | `(tactic| finite_iterator_tactic_trivial) => `(tactic| trivial)

/--
`finite_iterator_tactic` is the tactic automatically called by the notation `arr[i]`
to prove any side conditions that arise when constructing the term
(e.g. the index is in bounds of the array). It just delegates to
`finite_iterator_tactic_trivial` and gives a diagnostic error message otherwise;
users are encouraged to extend `finite_iterator_tactic_trivial` instead of this tactic.
-/
macro "finite_iterator_tactic" : tactic =>
  `(tactic| first
      /-
      Recall that `macro_rules` (namely, for `finite_iterator_tactic_trivial`) are tried in reverse order.
      We first, however, try `done`, since the necessary proof may already have been
      found during unification, in which case there is no goal to solve (see #6999).
      If a goal is present, we want `assumption` to be tried first.
      This is important for theorems such as
      ```
      [simp] theorem getElem_pop (a : Array α) (i : Nat) (hi : i < a.pop.size) :
      a.pop[i] = a[i]'(Nat.lt_of_lt_of_le (a.size_pop ▸ hi) (Nat.sub_le _ _)) :=
      ```
      There is a proof embedded in the right-hand-side, and we want it to be just `hi`.
      If `omega` is used to "fill" this proof, we will have a more complex proof term that
      cannot be inferred by unification.
      We hardcoded `assumption` here to ensure users cannot accidentally break this IF
      they add new `macro_rules` for `finite_iterator_tactic_trivial`.
      -/
    | done
    | assumption
    | finite_iterator_tactic_trivial
    | fail "failed to prove that the iterator is finite, possible solutions:
  - Use `have`-expressions to prove that the iterator is finite
  - Instead of `it.toList`, try `it.allowNontermination.toList`, which is partial and does not require a termination proof
  - Extend `finite_iterator_tactic_trivial` using `macro_rules`"
   )

@[always_inline, inline]
def IterM.showFinite [Iterator α m β] [Monad m] (it : IterM (α := α) m β) (h : it.IsFinite := by finite_iterator_tactic) :
    IterM (α := FiniteIterator it h) m β :=
  IterM.Advanced.lineage it

end Std.Iterators
