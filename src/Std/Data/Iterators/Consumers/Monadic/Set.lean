/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Init.Data.Iterators.Consumers.Monadic.Loop
public import Std.Data.HashSet.Basic
public import Std.Data.ExtHashSet.Basic
public import Std.Data.TreeSet.Basic
public import Std.Data.ExtTreeSet.Basic
import Init.Data.Iterators.Consumers.Monadic.Loop

set_option doc.verso true

namespace Std
open Iterators

set_option doc.verso false

/--
Traverses the given iterator and stores the emitted values in a {name}`HashSet`.

If the iterator is not finite, this function might run forever. Given {givenInstance}`Finite α m`,
the variant {lean}`it.ensureTermination.toHashSet` always terminates after finitely many steps.
-/
@[inline]
public def IterM.toHashSet {α β : Type w} [BEq β] [Hashable β] {m : Type w → Type w'} [Monad m]
    [Iterator α m β] [IteratorLoop α m m] (it : IterM (α := α) m β) : m (HashSet β) :=
  it.fold (init := ∅) fun acc a => acc.insert a

set_option doc.verso true

/--
Traverses the given iterator and stores the emitted values in a {name}`HashSet`.

This variant terminates after finitely many steps and requires a proof that the iterator is
finite. If such a proof is not available, consider using {name}`IterM.toHashSet`.
-/
@[inline]
public def IterM.Total.toHashSet {α β : Type w} [BEq β] [Hashable β] {m : Type w → Type w'} [Monad m]
    [Iterator α m β] [Finite α m] [IteratorLoop α m m] (it : IterM.Total (α := α) m β) :
    m (HashSet β) :=
  it.it.toHashSet

docs_to_verso IterM.toHashSet

set_option doc.verso false

/--
Traverses the given iterator and stores the emitted values in a {name}`ExtHashSet`.

If the iterator is not finite, this function might run forever. Given {givenInstance}`Finite α m`,
the variant {lean}`it.ensureTermination.toExtHashSet` always terminates after finitely many steps.
-/
@[inline]
public def IterM.toExtHashSet {α β : Type w} [BEq β] [Hashable β] [EquivBEq β] [LawfulHashable β]
    {m : Type w → Type w'} [Monad m] [Iterator α m β] [IteratorLoop α m m]
    (it : IterM (α := α) m β) : m (ExtHashSet β) :=
  it.fold (init := ∅) fun acc a => acc.insert a

set_option doc.verso true

/--
Traverses the given iterator and stores the emitted values in a {name}`ExtHashSet`.

This variant terminates after finitely many steps and requires a proof that the iterator is
finite. If such a proof is not available, consider using {name}`IterM.toExtHashSet`.
-/
@[inline]
public def IterM.Total.toExtHashSet {α β : Type w} [BEq β] [Hashable β] [EquivBEq β] [LawfulHashable β]
    {m : Type w → Type w'} [Monad m] [Iterator α m β] [Finite α m] [IteratorLoop α m m]
    (it : IterM.Total (α := α) m β) : m (ExtHashSet β) :=
  it.it.toExtHashSet

docs_to_verso IterM.toExtHashSet

set_option doc.verso false

/--
Traverses the given iterator and stores the emitted values in a {name}`TreeSet`.

If the iterator is not finite, this function might run forever. Given {givenInstance}`Finite α m`,
the variant {lean}`it.ensureTermination.toTreeSet` always terminates after finitely many steps.
-/
@[inline]
public def IterM.toTreeSet {α β : Type w} {m : Type w → Type w'} [Monad m]
    [Iterator α m β] [IteratorLoop α m m] (it : IterM (α := α) m β) (cmp : β → β → Ordering) :
    m (TreeSet β cmp) :=
  it.fold (init := ∅) fun acc a => acc.insert a

set_option doc.verso true

/--
Traverses the given iterator and stores the emitted values in a {name}`TreeSet`.

This variant terminates after finitely many steps and requires a proof that the iterator is
finite. If such a proof is not available, consider using {name}`IterM.toTreeSet`.
-/
@[inline]
public def IterM.Total.toTreeSet {α β : Type w} {m : Type w → Type w'} [Monad m]
    [Iterator α m β] [Finite α m] [IteratorLoop α m m] (it : IterM.Total (α := α) m β)
    (cmp : β → β → Ordering) : m (TreeSet β cmp) :=
  it.it.toTreeSet cmp

docs_to_verso IterM.toTreeSet

set_option doc.verso false

/--
Traverses the given iterator and stores the emitted values in a {name}`ExtTreeSet`.

If the iterator is not finite, this function might run forever. Given {givenInstance}`Finite α m`,
the variant {lean}`it.ensureTermination.toExtTreeSet cmp` always terminates after finitely
many steps.
-/
@[inline]
public def IterM.toExtTreeSet {α β : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β]
    [IteratorLoop α m m] (it : IterM (α := α) m β) (cmp : β → β → Ordering := by exact compare)
    [TransCmp cmp] : m (ExtTreeSet β cmp) :=
  it.fold (init := ∅) fun acc a => acc.insert a

set_option doc.verso true

/--
Traverses the given iterator and stores the emitted values in a {name}`ExtTreeSet`.

This variant terminates after finitely many steps and requires a proof that the iterator is
finite. If such a proof is not available, consider using {name}`IterM.toExtTreeSet`.
-/
@[inline]
public def IterM.Total.toExtTreeSet {α β : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β]
    [Finite α m] [IteratorLoop α m m] (it : IterM.Total (α := α) m β)
    (cmp : β → β → Ordering := by exact compare) [TransCmp cmp] : m (ExtTreeSet β cmp) :=
  it.it.toExtTreeSet cmp

docs_to_verso IterM.toExtTreeSet

end Std
