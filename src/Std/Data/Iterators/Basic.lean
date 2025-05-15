/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Init.Core
import Init.Classical
import Init.NotationExtra
import Init.TacticsExtra

namespace Std

namespace Iterators

structure IterM {α : Type w} (m : Type w → Type w') (β : Type v) : Type w where
  inner : α

structure Iter {α : Type w} (β : Type v) : Type w where
  inner : α

def Iter.toIterM {α : Type w} {β : Type w} (it : Iter (α := α) β) : IterM (α := α) Id β :=
  ⟨it.inner⟩

def IterM.toPureIter {α : Type w} {β : Type w} (it : IterM (α := α) Id β) : Iter (α := α) β :=
  ⟨it.inner⟩

@[simp]
theorem Iter.toPureIter_toIterM {α : Type w} {β : Type w} (it : Iter (α := α) β) :
    it.toIterM.toPureIter = it :=
  rfl

@[simp]
theorem Iter.toIterM_toPureIter {α : Type w} {β : Type w} (it : IterM (α := α) Id β) :
    it.toPureIter.toIterM = it :=
  rfl

section IterStep

variable {α : Type u} {β : Type w}

inductive IterStep (α β) where
| yield : (it : α) → (b : β) → IterStep α β
| skip : (a : α) → IterStep α β
| done : IterStep α β

def IterStep.successor : IterStep α β → Option α
  | .yield it _ => some it
  | .skip it => some it
  | .done => none

@[always_inline, inline]
def IterStep.map {α' : Type u'} {β' : Type v'} (f : α → α') (g : β → β') : IterStep α β → IterStep α' β'
  | .yield it out => .yield (f it) (g out)
  | .skip it => .skip (f it)
  | .done => .done

theorem IterStep.map_id {it : IterStep α β} :
    it.map id id = it := by
  simp only [map]
  cases it <;> simp

theorem IterStep.map_id' {it : IterStep α β} :
    it.map (·) (·) = it :=
  map_id

@[simp]
theorem IterStep.map_done {f : α → α'} {g : β → β'} :
  (.done : IterStep α β).map f g = .done := rfl

@[simp]
theorem IterStep.map_skip {f : α → α'} {g : β → β'} :
  (.skip it : IterStep α β).map f g = .skip (f it) := rfl

@[simp]
theorem IterStep.map_yield {f : α → α'} {g : β → β'} :
  (.yield it out : IterStep α β).map f g = .yield (f it) (g out) := rfl

theorem IterStep.map_map {α' : Type u'} {β' : Type v'} {f : α → α'} {g : β → β'}
    {α'' : Type u''} {β'' : Type v''} {f' : α' → α''} {g' : β' → β''} {it : IterStep α β} :
    (it.map f g).map f' g' = it.map (f · |> f') (g · |> g') := by
  simp only [map]
  cases it <;> simp

theorem IterStep.successor_map {α' : Type u'} {β' : Type v'} {f : α → α'} {g : β → β'} {step : IterStep α β} :
    (step.map f g).successor = step.successor.elim none (some <| f ·) := by
  cases step <;> rfl

def PlausibleIterStep (plausible_step : IterStep α β → Prop) := Subtype plausible_step

@[match_pattern]
def PlausibleIterStep.yield {plausible_step : IterStep α β → Prop}
    (it' : α) (out : β) (h : plausible_step (.yield it' out)) : PlausibleIterStep plausible_step :=
  ⟨.yield it' out, h⟩

@[match_pattern]
def PlausibleIterStep.skip {plausible_step : IterStep α β → Prop}
    (it' : α) (h : plausible_step (.skip it')) : PlausibleIterStep plausible_step :=
  ⟨.skip it', h⟩

@[match_pattern]
def PlausibleIterStep.done {plausible_step : IterStep α β → Prop}
    (h : plausible_step .done) : PlausibleIterStep plausible_step :=
  ⟨.done, h⟩

def PlausibleIterStep.successor (plausible_step : IterStep α β → Prop)
    (step : PlausibleIterStep plausible_step) : Option α :=
  step.val.successor

@[always_inline, inline]
def PlausibleIterStep.map {plausible_step : IterStep α β → Prop}
    {α' : Type u'} {β' : Type v'} (f : α → α') (g : β → β') (new_plausible_step : IterStep α' β' → Prop)
    (h : ∀ step : IterStep α β, plausible_step step → new_plausible_step (step.map f g))
    (step : PlausibleIterStep plausible_step) : PlausibleIterStep new_plausible_step :=
  ⟨step.val.map f g, h _ step.property⟩

theorem PlausibleIterStep.map_id {plausible_step : IterStep α β → Prop}
    {it : PlausibleIterStep plausible_step} :
    it.map id id plausible_step (by simp [IterStep.map_id]) = it := by
  simp only [map, IterStep.map]
  cases it <;> dsimp only <;> split <;> simp

end IterStep

class Iterator (α : Type w) (m : Type w → Type w') (β : outParam (Type w)) where
  plausible_step : IterM (α := α) m β → IterStep (IterM (α := α) m β) β → Prop
  step : (it : IterM (α := α) m β) → m (PlausibleIterStep <| plausible_step it)

section Monadic

@[always_inline, inline]
def toIter {α : Type w} (it : α) (m : Type w → Type w') (β : Type v) :
    IterM (α := α) m β :=
  ⟨it⟩

@[simp]
theorem toIter_inner {α m β} (it : IterM (α := α) m β) :
    toIter it.inner m β = it :=
  rfl

@[simp]
theorem inner_toIter {α m β} (it : α) :
    (toIter it m β).inner = it :=
  rfl

abbrev IterM.plausible_step {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β] :
    IterM (α := α) m β → IterStep (IterM (α := α) m β) β → Prop :=
  Iterator.plausible_step (α := α) (m := m)

abbrev IterM.Step {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    (it : IterM (α := α) m β) :=
  PlausibleIterStep it.plausible_step

def IterM.plausible_output {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    (it : IterM (α := α) m β) (out : β) : Prop :=
  ∃ it', it.plausible_step (.yield it' out)

def IterM.plausible_successor_of {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    (it' it : IterM (α := α) m β) : Prop :=
  ∃ step, step.successor = some it' ∧ it.plausible_step step

def IterM.plausible_skip_successor_of {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    (it' it : IterM (α := α) m β) : Prop :=
  it.plausible_step (.skip it')

def IterM.step {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    (it : IterM (α := α) m β) : m it.Step :=
  Iterator.step it

end Monadic

section Pure

def Iter.plausible_step {α : Type w} {β : Type w} [Iterator α Id β]
    (it : Iter (α := α) β) (step : IterStep (Iter (α := α) β) β) : Prop :=
  it.toIterM.plausible_step (step.map Iter.toIterM id)

def Iter.Step {α : Type w} {β : Type w} [Iterator α Id β] (it : Iter (α := α) β) :=
  PlausibleIterStep (Iter.plausible_step it)

def Iter.plausible_output {α : Type w} {β : Type w} [Iterator α Id β]
    (it : Iter (α := α) β) (out : β) : Prop :=
  ∃ it', it.plausible_step (.yield it' out)

def Iter.plausible_successor_of {α : Type w} {β : Type w} [Iterator α Id β]
    (it' it : Iter (α := α) β) : Prop :=
  ∃ step, step.successor = some it' ∧ it.plausible_step step

def Iter.plausible_skip_successor_of {α : Type w} {β : Type w} [Iterator α Id β]
    (it' it : Iter (α := α) β) : Prop :=
  it.plausible_step (.skip it')

@[always_inline, inline]
def Iter.step {α : Type w} {β : Type w} [Iterator α Id β]
    (it : Iter (α := α) β) : it.Step := by
  refine it.toIterM.step.run.map IterM.toPureIter id _ ?_
  intro step hp
  simp only [Iter.plausible_step, IterStep.map_map, id_eq, IterStep.map_id', toIterM_toPureIter, hp]

end Pure

section Finite

class Finite (α m) [Iterator α m β] : Prop where
  wf : WellFounded (IterM.plausible_successor_of (α := α) (m := m))

structure IterM.TerminationMeasures.Finite
    (α : Type w) (m : Type w → Type w') {β : Type w} [Iterator α m β] where
  it : IterM (α := α) m β

def IterM.TerminationMeasures.Finite.rel
    {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β] :
    TerminationMeasures.Finite α m → TerminationMeasures.Finite α m → Prop :=
  Relation.TransGen <| InvImage IterM.plausible_successor_of IterM.TerminationMeasures.Finite.it

instance {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    [Finite α m] : WellFoundedRelation (IterM.TerminationMeasures.Finite α m) where
  rel := IterM.TerminationMeasures.Finite.rel
  wf := (InvImage.wf _ Finite.wf).transGen

def IterM.finitelyManySteps {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    [Finite α m] (it : IterM (α := α) m β) : IterM.TerminationMeasures.Finite α m :=
  ⟨it⟩

theorem IterM.TerminationMeasures.Finite.rel_of_yield
    {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    {it it' : IterM (α := α) m β} {out : β} (h : it.plausible_step (.yield it' out)) :
    rel ⟨it'⟩ ⟨it⟩ := by
  exact .single ⟨_, rfl, h⟩

theorem IterM.TerminationMeasures.Finite.rel_of_skip
    {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    {it it' : IterM (α := α) m β} (h : it.plausible_step (.skip it')) :
    rel ⟨it'⟩ ⟨it⟩ := by
  exact .single ⟨_, rfl, h⟩

macro_rules | `(tactic| decreasing_trivial) => `(tactic|
  first
  | exact IterM.TerminationMeasures.Finite.rel_of_yield ‹_›
  | exact IterM.TerminationMeasures.Finite.rel_of_skip ‹_›)

def Iter.finitelyManySteps {α : Type w} {β : Type w} [Iterator α Id β] [Finite α Id]
    (it : Iter (α := α) β) : IterM.TerminationMeasures.Finite α Id :=
  it.toIterM.finitelyManySteps

theorem Iter.TerminationMeasures.Finite.rel_of_yield
    {α : Type w} {β : Type w} [Iterator α Id β]
    {it it' : Iter (α := α) β} {out : β} (h : it.plausible_step (.yield it' out)) :
    IterM.TerminationMeasures.Finite.rel ⟨it'.toIterM⟩ ⟨it.toIterM⟩ :=
  IterM.TerminationMeasures.Finite.rel_of_yield h

theorem Iter.TerminationMeasures.Finite.rel_of_skip
    {α : Type w} {β : Type w} [Iterator α Id β]
    {it it' : Iter (α := α) β} (h : it.plausible_step (.skip it')) :
    IterM.TerminationMeasures.Finite.rel ⟨it'.toIterM⟩ ⟨it.toIterM⟩ :=
  IterM.TerminationMeasures.Finite.rel_of_skip h

macro_rules | `(tactic| decreasing_trivial) => `(tactic|
  first
  | exact Iter.TerminationMeasures.Finite.rel_of_yield ‹_›
  | exact Iter.TerminationMeasures.Finite.rel_of_skip ‹_›)

end Finite

section Productive

class Productive (α m) {β} [Iterator α m β] : Prop where
  wf : WellFounded (IterM.plausible_skip_successor_of (α := α) (m := m))

structure IterM.TerminationMeasures.Productive
    (α : Type w) (m : Type w → Type w') {β : Type w} [Iterator α m β] where
  it : IterM (α := α) m β

def IterM.TerminationMeasures.Productive.rel
    {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β] :
    TerminationMeasures.Productive α m → TerminationMeasures.Productive α m → Prop :=
  Relation.TransGen <| InvImage IterM.plausible_skip_successor_of IterM.TerminationMeasures.Productive.it

instance {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    [Productive α m] : WellFoundedRelation (IterM.TerminationMeasures.Productive α m) where
  rel := IterM.TerminationMeasures.Productive.rel
  wf := (InvImage.wf _ Productive.wf).transGen

def IterM.finitelyManySkips {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    [Productive α m] (it : IterM (α := α) m β) : IterM.TerminationMeasures.Productive α m :=
  ⟨it⟩

theorem IterM.TerminationMeasures.Productive.rel_of_skip
    {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    {it it' : IterM (α := α) m β} (h : it.plausible_step (.skip it')) :
    rel ⟨it'⟩ ⟨it⟩ :=
  .single h

macro_rules | `(tactic| decreasing_trivial) => `(tactic|
  exact IterM.TerminationMeasures.Productive.rel_of_skip ‹_›)

def Iter.finitelyManySkips {α : Type w} {β : Type w} [Iterator α Id β] [Productive α Id]
    (it : Iter (α := α) β) : IterM.TerminationMeasures.Productive α Id :=
  it.toIterM.finitelyManySkips

theorem Iter.TerminationMeasures.Productive.rel_of_skip
    {α : Type w} {β : Type w} [Iterator α Id β]
    {it it' : Iter (α := α) β} (h : it.plausible_step (.skip it')) :
    IterM.TerminationMeasures.Productive.rel ⟨it'.toIterM⟩ ⟨it.toIterM⟩ :=
  IterM.TerminationMeasures.Productive.rel_of_skip h

macro_rules | `(tactic| decreasing_trivial) => `(tactic|
  exact Iter.TerminationMeasures.Productive.rel_of_skip ‹_›)

end Productive

end Iterators

export Iterators (Iter IterM)

end Std
