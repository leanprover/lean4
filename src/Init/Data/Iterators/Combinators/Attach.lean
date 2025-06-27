/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
import Init.Data.Iterators.Combinators.Monadic.Attach
import Init.Data.Iterators.Combinators.FilterMap

namespace Std.Iterators

@[always_inline, inline]
def Types.Attach.modifyStep {α : Type w} {β : Type w} [Iterator α Id β]
    {P : β → Prop} (it : Iter (α := Types.Attach α Id P) { out : β // P out })
    (step : it.internalState.inner.toIter.Step (α := α)) :
    IterStep (Iter (α := Attach α Id P) { out : β // P out })
        { out : β // P out } :=
  (Monadic.modifyStep it.toIterM step.toMonadic).mapIterator IterM.toIter
  -- match step with
  -- | .yield it' out h =>
  --   .yield ⟨it'.toIterM, fun out ho => it.internalState.invariant out (.indirect ⟨_, rfl, h⟩ ho)⟩
  --     ⟨out, it.internalState.invariant out (.direct ⟨_, h⟩)⟩
  -- | .skip it' h =>
  --   .skip ⟨it'.toIterM, fun out ho => it.internalState.invariant out (.indirect ⟨_, rfl, h⟩ ho)⟩
  -- | .done _ => .done

@[always_inline, inline, expose, inherit_doc IterM.attachWith]
def Iter.attachWith {α β : Type w}
    [Iterator α Id β]
    (it : Iter (α := α) β) (P : β → Prop) (h : ∀ out, it.IsPlausibleIndirectOutput out → P out) :
  Iter (α := Types.Attach α Id P) { out : β // P out } :=
  (it.toIterM.attachWith P ?h).toIter
where finally
  case h =>
    simp only [← isPlausibleIndirectOutput_iff_isPlausibleIndirectOutput_toIterM]
    exact h

end Std.Iterators
