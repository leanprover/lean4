/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
import Init.Data.Iterators.Basic
import Init.Data.Iterators.Consumers.Partial
import Init.Data.Iterators.Consumers.Monadic.Collect

/-!
# Collectors

This module provides consumers that collect the values emitted by an iterator in a data structure.
Concretely, the following operations are provided:

* `Iter.toList`, collecting the values in a list
* `Iter.toListRev`, collecting the values in a list in reverse order but more efficiently
* `Iter.toArray`, collecting the values in an array

Some operations are implemented using the `IteratorCollect` and `IteratorCollectPartial`
typeclasses.
-/

namespace Std.Iterators

@[always_inline, inline, inherit_doc IterM.toArray]
def Iter.toArray {α : Type w} {β : Type w}
    [Iterator α Id β] [Finite α Id] [IteratorCollect α Id Id] (it : Iter (α := α) β) : Array β :=
  it.toIterM.toArray.run

@[always_inline, inline, inherit_doc IterM.Partial.toArray]
def Iter.Partial.toArray {α : Type w} {β : Type w}
    [Iterator α Id β] [IteratorCollectPartial α Id Id] (it : Iter.Partial (α := α) β) : Array β :=
  it.it.toIterM.allowNontermination.toArray.run

@[always_inline, inline, inherit_doc IterM.toListRev]
def Iter.toListRev {α : Type w} {β : Type w}
    [Iterator α Id β] [Finite α Id] (it : Iter (α := α) β) : List β :=
  it.toIterM.toListRev.run

@[always_inline, inline, inherit_doc IterM.Partial.toListRev]
def Iter.Partial.toListRev {α : Type w} {β : Type w}
    [Iterator α Id β] (it : Iter.Partial (α := α) β) : List β :=
  it.it.toIterM.allowNontermination.toListRev.run

@[always_inline, inline, inherit_doc IterM.toList]
def Iter.toList {α : Type w} {β : Type w}
    [Iterator α Id β] [Finite α Id] [IteratorCollect α Id Id] (it : Iter (α := α) β) : List β :=
  it.toIterM.toList.run

@[always_inline, inline, inherit_doc IterM.Partial.toList]
def Iter.Partial.toList {α : Type w} {β : Type w}
    [Iterator α Id β] [IteratorCollectPartial α Id Id] (it : Iter.Partial (α := α) β) : List β :=
  it.it.toIterM.allowNontermination.toList.run

/--
This class charaterizes how the plausibility behavior (`IsPlausibleStep`) and the actual iteration
behavior (`it.step`) should relate to each other for pure iterators. Intuitively, a step should
only be plausible if it is possible. For simplicity's sake, the actual definition is weaker but
presupposes that the iterator is finite.

This is an experimental instance and it should not be explicitly used downstream of the standard
library.
-/
class LawfulPureIterator (α : Type w) [Iterator α Id β]
    [Finite α Id] [IteratorCollect α Id Id] where
  mem_toList_iff_isPlausibleIndirectOutput {it : Iter (α := α) β} {out : β} :
    out ∈ it.toList ↔ it.IsPlausibleIndirectOutput out

end Std.Iterators
