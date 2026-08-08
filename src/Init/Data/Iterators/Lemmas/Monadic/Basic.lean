/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Basic
import Init.RCases

public section

namespace Std.IterM
open Std.Iterators

/--
Induction principle for finite monadic iterators: One can define a function `f` that maps every
iterator `it` to an element of `motive it` by defining `f it` in terms of the values of `f` on
the plausible successors of `it'.
-/
@[specialize]
def inductSteps {α m β} [Iterator α m β] [Finite α m]
  (motive : IterM (α := α) m β → Sort x)
  (step : (it : IterM (α := α) m β) →
    (ih_yield : ∀ {it' : IterM (α := α) m β} {out : β},
      it.IsPlausibleStep (.yield it' out) → motive it') →
    (ih_skip : ∀ {it' : IterM (α := α) m β}, it.IsPlausibleStep (.skip it') → motive it') →
    motive it)
  (it : IterM (α := α) m β) : motive it :=
  step it
    (fun {it' _} _ => inductSteps motive step it')
    (fun {it'} _ => inductSteps motive step it')
termination_by it.finitelyManySteps

/--
Induction principle for productive monadic iterators: One can define a function `f` that maps every
iterator `it` to an element of `motive it` by defining `f it` in terms of the values of `f` on
the plausible skip successors of `it'.
-/
@[specialize]
def inductSkips {α m β} [Iterator α m β] [Productive α m]
  (motive : IterM (α := α) m β → Sort x)
  (step : (it : IterM (α := α) m β) →
    (ih_skip : ∀ {it' : IterM (α := α) m β}, it.IsPlausibleStep (.skip it') → motive it') →
    motive it)
  (it : IterM (α := α) m β) : motive it :=
  step it (fun {it'} _ => inductSkips motive step it')
termination_by it.finitelyManySkips

-- Not a real instance because the discrimination key would be to indiscriminate.
local instance [Iterator α Id β] [LawfulDeterministicIterator α Id] {it : IterM (α := α) Id β} :
    Subsingleton it.Step where
  allEq s s' := by
    obtain ⟨s'', hs''⟩ := LawfulDeterministicIterator.isPlausibleStep_eq_eq it
    obtain ⟨s, hs⟩ := s
    obtain ⟨s', hs'⟩ := s'
    simp only [hs''] at hs hs'
    have := hs.trans hs'.symm
    rwa [Subtype.mk.injEq]

theorem IsPlausibleStep.eq_step [Iterator α Id β] [LawfulDeterministicIterator α Id]
    {it : IterM (α := α) Id β} {step} (h : it.IsPlausibleStep step) :
    step = it.step.run.inflate.val := by
  have : ⟨step, h⟩ = it.step.run.inflate := Subsingleton.allEq _ _
  simp [← this]

end Std.IterM
