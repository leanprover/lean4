/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Basic
public import Init.RCases

public section

namespace Std.Iter
open Std.Iterators

/--
Induction principle for finite iterators: One can define a function `f` that maps every
iterator `it` to an element of `motive it` by defining `f it` in terms of the values of `f` on
the plausible successors of `it'.
-/
@[specialize]
def inductSteps {α β} [Iterator α Id β] [Finite α Id]
  (motive : Iter (α := α) β → Sort x)
  (step : (it : Iter (α := α) β) →
    (ih_yield : ∀ {it' : Iter (α := α) β} {out : β},
      it.IsPlausibleStep (.yield it' out) → motive it') →
    (ih_skip : ∀ {it' : Iter (α := α) β}, it.IsPlausibleStep (.skip it') → motive it') →
    motive it)
  (it : Iter (α := α) β) : motive it :=
  step it
    (fun {it' _} _ => inductSteps motive step it')
    (fun {it'} _ => inductSteps motive step it')
termination_by it.finitelyManySteps

/--
Induction principle for productive iterators: One can define a function `f` that maps every
iterator `it` to an element of `motive it` by defining `f it` in terms of the values of `f` on
the plausible skip successors of `it'.
-/
@[specialize]
def inductSkips {α β} [Iterator α Id β] [Productive α Id]
  (motive : Iter (α := α) β → Sort x)
  (step : (it : Iter (α := α) β) →
    (ih_skip : ∀ {it' : Iter (α := α) β}, it.IsPlausibleStep (.skip it') → motive it') →
    motive it)
  (it : Iter (α := α) β) : motive it :=
  step it (fun {it'} _ => inductSkips motive step it')
termination_by it.finitelyManySkips

-- Not a real instance because the discrimination key would be to indiscriminate.
local instance [Iterator α Id β] [LawfulDeterministicIterator α Id] {it : Iter (α := α) β} :
    Subsingleton it.Step where
  allEq s s' := by
    obtain ⟨s'', hs''⟩ := LawfulDeterministicIterator.isPlausibleStep_eq_eq it.toIterM
    obtain ⟨s, hs⟩ := s
    obtain ⟨s', hs'⟩ := s'
    simp only [Iter.IsPlausibleStep, hs''] at hs hs'
    have := hs.trans hs'.symm
    rw [IterStep.mapIterator_inj (fun _ _ => toIterM_inj.mp) ] at this
    rwa [Subtype.mk.injEq]

theorem IsPlausibleStep.eq_step [Iterator α Id β] [LawfulDeterministicIterator α Id]
    {it : Iter (α := α) β} {step} (h : it.IsPlausibleStep step) :
    step = it.step.val := by
  have : ⟨step, h⟩ = it.step := Subsingleton.allEq _ _
  simp [← this]

end Std.Iter
