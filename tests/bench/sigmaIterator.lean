module

public import Std

/-!
This benchmark implements an iterator with a `Sigma` state, where the types of the second component
are themselves iterators with a state type dependent on the first component.

As of writing, the compiler generates forbiddingly bad code for it, so this is a benchmark
for the specializer.
-/

public section

namespace Std.Iterators.Types

/--
Internal state of the `sigma` combinator. Do not depend on its internals.
-/
@[unbox]
structure SigmaIterator (γ : Type w) (α : γ → Type w) where
  parameter : γ
  inner : α parameter

@[always_inline, inline]
def SigmaIterator.Monadic.modifyStep {β γ : Type w} {α : γ → Type w} {m : Type w → Type w'}
    [∀ x : γ, Iterator (α := α x) m β]
    (it : IterM (α := SigmaIterator γ α) m β)
    (step : (IterM.mk it.internalState.inner m β).Step) :
    IterStep (IterM (α := SigmaIterator γ α) m β) β :=
  match step.val with
  | .yield it' out =>
    .yield ⟨it.internalState.parameter, it'.internalState⟩ out
  | .skip it' =>
    .skip ⟨it.internalState.parameter, it'.internalState⟩
  | .done => .done

instance SigmaIterator.instIterator {γ : Type w} {α : γ → Type w}
    [∀ x : γ, Iterator (α := α x) m β] [Monad m] :
    Iterator (SigmaIterator γ α) m β where
  IsPlausibleStep it step := ∃ step', Monadic.modifyStep it step' = step
  step it :=
    (fun step => .deflate ⟨Monadic.modifyStep it step.inflate, step.inflate, rfl⟩) <$>
      (IterM.mk it.internalState.inner m β).step

private structure SigmaIteratorWF (γ : Type w) (α : γ → Type w) (m : Type w → Type w) (β : Type w) where
  parameter : γ
  it : IterM (α := α parameter) m β

private def SigmaIterator.instFinitenessRelation {γ : Type w} {α : γ → Type w}
    [∀ x : γ, Iterator (α x) m β] [∀ x : γ, Finite (α x) m] [Monad m] :
    FinitenessRelation (SigmaIterator γ α) m where
  Rel := InvImage
    (PSigma.Lex emptyRelation
      (β := fun param : γ => IterM (α := α param) m β)
      (fun _ => InvImage IterM.TerminationMeasures.Finite.Rel IterM.finitelyManySteps))
    (fun it => ⟨it.internalState.parameter, IterM.mk it.internalState.inner m β⟩)
  wf := by
    apply InvImage.wf
    refine ⟨fun ⟨param, it⟩ => ?_⟩
    apply PSigma.lexAccessible
    · exact emptyWf.wf.apply param
    · exact fun param' => InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    obtain ⟨_, hs, step, h', rfl⟩ := h
    cases step using PlausibleIterStep.casesOn
    · cases hs
      apply PSigma.Lex.right
      exact IterM.TerminationMeasures.Finite.rel_of_yield ‹_›
    · cases hs
      apply PSigma.Lex.right
      exact IterM.TerminationMeasures.Finite.rel_of_skip ‹_›
    · cases hs

instance SigmaIterator.instFinite {γ : Type w} {α : γ → Type w}
    [∀ x : γ, Iterator (α x) m β] [∀ x : γ, Finite (α x) m] [Monad m] :
    Finite (SigmaIterator γ α) m :=
  .of_finitenessRelation instFinitenessRelation

private def SigmaIterator.instProductivenessRelation {γ : Type w} {α : γ → Type w}
    [∀ x : γ, Iterator (α x) m β] [∀ x : γ, Productive (α x) m] [Monad m] :
    ProductivenessRelation (SigmaIterator γ α) m where
  Rel := InvImage
    (PSigma.Lex emptyRelation
      (β := fun param : γ => IterM (α := α param) m β)
      (fun _ => InvImage IterM.TerminationMeasures.Productive.Rel IterM.finitelyManySkips))
    (fun it => ⟨it.internalState.parameter, IterM.mk it.internalState.inner m β⟩)
  wf := by
    apply InvImage.wf
    refine ⟨fun ⟨param, it⟩ => ?_⟩
    apply PSigma.lexAccessible
    · exact emptyWf.wf.apply param
    · exact fun param' => InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    obtain ⟨step, hs⟩ := h
    cases step using PlausibleIterStep.casesOn
    · cases hs
    · cases hs
      apply PSigma.Lex.right
      exact IterM.TerminationMeasures.Productive.rel_of_skip ‹_›
    · cases hs

instance SigmaIterator.instProductive {γ : Type w} {α : γ → Type w}
    [∀ x : γ, Iterator (α x) m β] [∀ x : γ, Productive (α x) m] [Monad m] :
    Productive (SigmaIterator γ α) m :=
  .of_productivenessRelation instProductivenessRelation

instance SigmaIterator.instIteratorLoop {γ : Type w} {α : γ → Type w}
    [∀ x : γ, Iterator (α x) m β] [Monad m] [Monad n] :
    IteratorLoop (SigmaIterator γ α) m n :=
  .defaultImplementation

end Types

/--
If the state `α param` of an iterator `it` is dependent on some parameter `param`, creates an iterator
whose state is equivalent to the `Sigma` type `(param : γ) × α param`, getting rid of the type
dependency at the cost of storing the parameter in a structure field at runtime.

**Termination properties:**

* `Finite` instance: only if the base iterator is finite
* `Productive` instance: only if the base iterator is productive
-/
@[always_inline, inline, expose]
def IterM.sigma {γ : Type w} {α : γ → Type w}
    [∀ x : γ, Iterator (α x) m β] {param : γ} (it : IterM (α := α param) m β) :
    IterM (α := Types.SigmaIterator γ α) m β :=
  IterM.mk ⟨param, it.internalState⟩ m β

end Std.Iterators

open Std Std.Iterators Std.Iterators.Types

@[always_inline, inline, expose]
def Std.Iter.sigma {γ : Type w} {α : γ → Type w}
    [∀ x : γ, Iterator (α x) Id β] {param : γ} (it : Iter (α := α param) β):
    Iter (α := SigmaIterator γ α) β :=
  ⟨param, it.internalState⟩

partial def f [Iterator α Id Nat] (it : Iter (α := α) Nat) (acc : Nat) : Id Nat := do
  match it.step.val with
  | .yield it' out => f it' (acc + out)
  | .skip it' => f it' acc
  | .done => return acc

/--
This generates bad code such as:

```text
def f._at_.g.spec_0._redArg _x.1 _x.2 _x.3 it : Nat :=
  cases _x.3 : Nat
  | Monad.mk toApplicative toBind =>
    cases toApplicative : Nat
    | Applicative.mk toFunctor toPure toSeq toSeqLeft toSeqRight =>
      cases it : Nat
      | Sigma.mk fst snd =>
        cases toFunctor : Nat
        | Functor.mk map mapConst =>
          cases snd : Nat
          | Std.Rxo.Iterator.mk next upperBound =>
            let _f.4 := f._at_.g.spec_0._redArg._lam_0 it;
            let _f.5 := f._at_.g.spec_0._redArg._lam_2 toPure _x.2 toBind;
...
```
-/
def g : Nat := Id.run do
  (*...30000000).iter.filter (fun _ => True)
    |>.sigma (α := fun _ => _) (param := 0)
    |> f (acc := 0)

def main : IO Unit :=
  IO.println g
