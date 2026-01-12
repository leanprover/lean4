/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Consumers.Collect
public import Init.Data.Iterators.Consumers.Monadic.Loop

set_option linter.missingDocs true

public section

/-!
# Loop consumers

This module provides consumers that iterate over a given iterator, applying a certain user-supplied
function in every iteration. Concretely, the following operations are provided:

* `ForIn` instances
* `Iter.fold`, the analogue of `List.foldl`
* `Iter.foldM`, the analogue of `List.foldlM`

These operations are implemented using the `IteratorLoop` type class.
-/

namespace Std
open Std.Iterators

/--
A `ForIn'` instance for iterators. Its generic membership relation is not easy to use,
so this is not marked as `instance`. This way, more convenient instances can be built on top of it
or future library improvements will make it more comfortable.
-/
@[always_inline, inline]
def Iter.instForIn' {α : Type w} {β : Type w} {n : Type x → Type x'} [Monad n]
    [Iterator α Id β] [IteratorLoop α Id n] :
    ForIn' n (Iter (α := α) β) β ⟨fun it out => it.IsPlausibleIndirectOutput out⟩ where
  forIn' it init f :=
    IteratorLoop.finiteForIn' (fun _ _ f c => f c.run) |>.forIn' it.toIterM init
        fun out h acc =>
          f out (Iter.isPlausibleIndirectOutput_iff_isPlausibleIndirectOutput_toIterM.mpr h) acc

instance (α : Type w) (β : Type w) (n : Type x → Type x') [Monad n]
    [Iterator α Id β] [IteratorLoop α Id n] :
    ForIn n (Iter (α := α) β) β :=
  haveI : ForIn' n (Iter (α := α) β) β _ := Iter.instForIn'
  instForInOfForIn'

/--
An implementation of `for h : ... in ... do ...` notation for partial iterators.
-/
@[always_inline, inline]
def Iter.Partial.instForIn' {α : Type w} {β : Type w} {n : Type x → Type x'} [Monad n]
    [Iterator α Id β] [IteratorLoop α Id n] :
    ForIn' n (Iter.Partial (α := α) β) β ⟨fun it out => it.it.IsPlausibleIndirectOutput out⟩ where
  forIn' it init f :=
    haveI := @Iter.instForIn'
    forIn' it.it init f

instance (α : Type w) (β : Type w) (n : Type x → Type x') [Monad n]
    [Iterator α Id β] [IteratorLoop α Id n] :
    ForIn n (Iter.Partial (α := α) β) β :=
  haveI : ForIn' n (Iter.Partial (α := α) β) β _ := Iter.Partial.instForIn'
  instForInOfForIn'

/--
A `ForIn'` instance for iterators that is guaranteed to terminate after finitely many steps.
It is not marked as an instance because the membership predicate is difficult to work with.
-/
@[always_inline, inline]
def Iter.Total.instForIn' {α : Type w} {β : Type w} {n : Type x → Type x'} [Monad n]
    [Iterator α Id β] [IteratorLoop α Id n] [Finite α Id] :
    ForIn' n (Iter.Total (α := α) β) β ⟨fun it out => it.it.IsPlausibleIndirectOutput out⟩ where
  forIn' it init f := Iter.instForIn'.forIn' it.it init f

instance (α : Type w) (β : Type w) (n : Type x → Type x') [Monad n]
    [Iterator α Id β] [IteratorLoop α Id n] [Finite α Id] :
    ForIn n (Iter.Total (α := α) β) β :=
  haveI : ForIn' n (Iter.Total (α := α) β) β _ := Iter.Total.instForIn'
  instForInOfForIn'

instance {m : Type x → Type x'}
    {α : Type w} {β : Type w} [Iterator α Id β] [IteratorLoop α Id m] [Monad m] :
    ForM m (Iter (α := α) β) β where
  forM it f := forIn it PUnit.unit (fun out _ => do f out; return .yield .unit)

instance {m : Type x → Type x'}
    {α : Type w} {β : Type w} [Iterator α Id β] [IteratorLoop α Id m] [Monad m] :
    ForM m (Iter.Partial (α := α) β) β where
  forM it f := forIn it PUnit.unit (fun out _ => do f out; return .yield .unit)

instance {m : Type x → Type x'}
    {α : Type w} {β : Type w} [Monad m] [Iterator α Id β] [IteratorLoop α Id m] [Finite α Id] :
    ForM m (Iter.Total (α := α) β) β where
  forM it f := forIn it PUnit.unit (fun out _ => do f out; return .yield .unit)

/--
Folds a monadic function over an iterator from the left, accumulating a value starting with `init`.
The accumulated value is combined with the each element of the list in order, using `f`.

It is equivalent to `it.toList.foldlM`.
-/
@[always_inline, inline]
def Iter.foldM {m : Type x → Type x'} [Monad m]
    {α : Type w} {β : Type w} {γ : Type x} [Iterator α Id β]
    [IteratorLoop α Id m] (f : γ → β → m γ)
    (init : γ) (it : Iter (α := α) β) : m γ :=
  ForIn.forIn it init (fun x acc => ForInStep.yield <$> f acc x)

/--
Folds a monadic function over an iterator from the left, accumulating a value starting with `init`.
The accumulated value is combined with the each element of the list in order, using `f`.

It is equivalent to `it.toList.foldlM`.

This function is deprecated. Instead of `it.allowNontermination.foldM`, use `it.foldM`.
-/
@[always_inline, inline, deprecated Iter.foldM (since := "2025-12-04")]
def Iter.Partial.foldM {m : Type x → Type x'} [Monad m]
    {α : Type w} {β : Type w} {γ : Type x} [Iterator α Id β]
    [IteratorLoop α Id m] (f : γ → β → m γ)
    (init : γ) (it : Iter.Partial (α := α) β) : m γ :=
  it.it.foldM (init := init) f

/--
Folds a monadic function over an iterator from the left, accumulating a value starting with `init`.
The accumulated value is combined with the each element of the list in order, using `f`.

It is equivalent to `it.toList.foldlM`.

This variant terminates after finitely many steps and requires a proof that the iterator is
finite. If such a proof is not available, consider using `Iter.foldM`.
-/
@[always_inline, inline]
def Iter.Total.foldM {m : Type x → Type x'} [Monad m]
    {α : Type w} {β : Type w} {γ : Type x} [Iterator α Id β]
    [IteratorLoop α Id m] [Finite α Id] (f : γ → β → m γ)
    (init : γ) (it : Iter.Total (α := α) β) : m γ :=
  it.it.foldM (init := init) f

/--
Folds a function over an iterator from the left, accumulating a value starting with `init`.
The accumulated value is combined with the each element of the list in order, using `f`.

It is equivalent to `it.toList.foldl`.
-/
@[always_inline, inline]
def Iter.fold {α : Type w} {β : Type w} {γ : Type x} [Iterator α Id β]
    [IteratorLoop α Id Id] (f : γ → β → γ)
    (init : γ) (it : Iter (α := α) β) : γ :=
  ForIn.forIn (m := Id) it init (fun x acc => ForInStep.yield (f acc x))

/--
Folds a function over an iterator from the left, accumulating a value starting with `init`.
The accumulated value is combined with the each element of the list in order, using `f`.

It is equivalent to `it.toList.foldl`.

This function is deprecated. Instead of `it.allowNontermination.fold`, use `it.fold`.
-/
@[always_inline, inline, deprecated Iter.fold (since := "2025-12-04")]
def Iter.Partial.fold {α : Type w} {β : Type w} {γ : Type x} [Iterator α Id β]
    [IteratorLoop α Id Id] (f : γ → β → γ)
    (init : γ) (it : Iter.Partial (α := α) β) : γ :=
  it.it.fold (init := init) f

/--
Folds a function over an iterator from the left, accumulating a value starting with `init`.
The accumulated value is combined with the each element of the list in order, using `f`.

It is equivalent to `it.toList.foldl`.

This variant terminates after finitely many steps and requires a proof that the iterator is
finite. If such a proof is not available, consider using `Iter.fold`.
-/
@[always_inline, inline]
def Iter.Total.fold {α : Type w} {β : Type w} {γ : Type x} [Iterator α Id β]
    [IteratorLoop α Id Id] [Finite α Id] (f : γ → β → γ)
    (init : γ) (it : Iter.Total (α := α) β) : γ :=
  it.it.fold (init := init) f

set_option doc.verso true in
/--
Returns {lean}`true` if the monadic predicate {name}`p` returns {lean}`true` for
any element emitted by the iterator {name}`it`.

{lit}`O(|xs|)`. Short-circuits upon encountering the first match. The elements in {name}`it` are
examined in order of iteration.
-/
@[always_inline]
def Iter.anyM {α β : Type w} {m : Type → Type w'} [Monad m]
    [Iterator α Id β] [IteratorLoop α Id m]
    (p : β → m Bool) (it : Iter (α := α) β) : m Bool :=
  ForIn.forIn it false (fun x _ => do
    if ← p x then
      return .done true
    else
      return .yield false)

set_option doc.verso true in
/--
Returns {lean}`true` if the monadic predicate {name}`p` returns {lean}`true` for
any element emitted by the iterator {name}`it`.

{lit}`O(|xs|)`. Short-circuits upon encountering the first match. The elements in {name}`it` are
examined in order of iteration.

This variant terminates after finitely many steps and requires a proof that the iterator is
finite. If such a proof is not available, consider using {name}`Iter.anyM`.
-/
@[always_inline, inline]
def Iter.Total.anyM {α β : Type w} {m : Type → Type w'} [Monad m]
    [Iterator α Id β] [IteratorLoop α Id m] [Finite α Id]
    (p : β → m Bool) (it : Iter.Total (α := α) β) : m Bool :=
  it.it.anyM p

set_option doc.verso true in
/--
Returns {lean}`true` if the pure predicate {name}`p` returns {lean}`true` for
any element emitted by the iterator {name}`it`.

{lit}`O(|xs|)`. Short-circuits upon encountering the first match. The elements in {name}`it` are
examined in order of iteration.
-/
@[inline]
def Iter.any {α β : Type w}
    [Iterator α Id β] [IteratorLoop α Id Id]
    (p : β → Bool) (it : Iter (α := α) β) : Bool :=
  (it.anyM (fun x => pure (f := Id) (p x))).run

set_option doc.verso true in
/--
Returns {lean}`true` if the pure predicate {name}`p` returns {lean}`true` for
any element emitted by the iterator {name}`it`.

{lit}`O(|xs|)`. Short-circuits upon encountering the first match. The elements in {name}`it` are
examined in order of iteration.

This variant terminates after finitely many steps and requires a proof that the iterator is
finite. If such a proof is not available, consider using {name}`Iter.any`.
-/
@[inline]
def Iter.Total.any {α β : Type w}
    [Iterator α Id β] [IteratorLoop α Id Id] [Finite α Id]
    (p : β → Bool) (it : Iter.Total (α := α) β) : Bool :=
  it.it.any p

set_option doc.verso true in
/--
Returns {lean}`true` if the monadic predicate {name}`p` returns {lean}`true` for
all element emitted by the iterator {name}`it`.

{lit}`O(|xs|)`. Short-circuits upon encountering the first match. The elements in {name}`it` are
examined in order of iteration.
-/
@[always_inline, inline]
def Iter.allM {α β : Type w} {m : Type → Type w'} [Monad m]
    [Iterator α Id β] [IteratorLoop α Id m]
    (p : β → m Bool) (it : Iter (α := α) β) : m Bool :=
  ForIn.forIn it true (fun x _ => do
    if ← p x then
      return .yield true
    else
      return .done false)

set_option doc.verso true in
/--
Returns {lean}`true` if the monadic predicate {name}`p` returns {lean}`true` for
all element emitted by the iterator {name}`it`.

{lit}`O(|xs|)`. Short-circuits upon encountering the first match. The elements in {name}`it` are
examined in order of iteration.

This variant terminates after finitely mall steps and requires a proof that the iterator is
finite. If such a proof is not available, consider using {name}`Iter.allM`.
-/
@[always_inline, inline]
def Iter.Total.allM {α β : Type w} {m : Type → Type w'} [Monad m]
    [Iterator α Id β] [IteratorLoop α Id m] [Finite α Id]
    (p : β → m Bool) (it : Iter.Total (α := α) β) : m Bool :=
  it.it.allM p

set_option doc.verso true in
/--
Returns {lean}`true` if the pure predicate {name}`p` returns {lean}`true` for
all element emitted by the iterator {name}`it`.

{lit}`O(|xs|)`. Short-circuits upon encountering the first match. The elements in {name}`it` are
examined in order of iteration.
-/
@[inline]
def Iter.all {α β : Type w}
    [Iterator α Id β] [IteratorLoop α Id Id]
    (p : β → Bool) (it : Iter (α := α) β) : Bool :=
  (it.allM (fun x => pure (f := Id) (p x))).run

set_option doc.verso true in
/--
Returns {lean}`true` if the pure predicate {name}`p` returns {lean}`true` for
all element emitted by the iterator {name}`it`.

{lit}`O(|xs|)`. Short-circuits upon encountering the first match. The elements in {name}`it` are
examined in order of iteration.

This variant terminates after finitely mall steps and requires a proof that the iterator is
finite. If such a proof is not available, consider using {name}`Iter.all`.
-/
@[inline]
def Iter.Total.all {α β : Type w}
    [Iterator α Id β] [IteratorLoop α Id Id] [Finite α Id]
    (p : β → Bool) (it : Iter.Total (α := α) β) : Bool :=
  it.it.all p

/--
Returns the first non-`none` result of applying the monadic function `f` to each output
of the iterator, in order. Returns `none` if `f` returns `none` for all outputs.

`O(|it|)`. Short-circuits when `f` returns `some _`. The outputs of `it` are
examined in order of iteration.

If the iterator is not finite, this function might run forever. The variant
`it.ensureTermination.findSomeM?` always terminates after finitely many steps.

Example:
```lean example
#eval [7, 6, 5, 8, 1, 2, 6].iter.findSomeM? fun i => do
  if i < 5 then
    return some (i * 10)
  if i ≤ 6 then
    IO.println s!"Almost! {i}"
  return none
```
```output
Almost! 6
Almost! 5
```
```output
some 10
```
-/
@[inline]
def Iter.findSomeM? {α β : Type w} {γ : Type x} {m : Type x → Type w'} [Monad m] [Iterator α Id β]
    [IteratorLoop α Id m] (it : Iter (α := α) β) (f : β → m (Option γ)) :
    m (Option γ) :=
  ForIn.forIn it none (fun x _ => do
    match ← f x with
    | none => return .yield none
    | some fx => return .done (some fx))

/--
Returns the first non-`none` result of applying the monadic function `f` to each output
of the iterator, in order. Returns `none` if `f` returns `none` for all outputs.

`O(|it|)`. Short-circuits when `f` returns `some _`. The outputs of `it` are
examined in order of iteration.

This function is deprecated. Instead of `it.allowNontermination.findSomeM?`, use `it.findSomeM?`.

Example:
```lean example
#eval [7, 6, 5, 8, 1, 2, 6].iter.findSomeM? fun i => do
  if i < 5 then
    return some (i * 10)
  if i ≤ 6 then
    IO.println s!"Almost! {i}"
  return none
```
```output
Almost! 6
Almost! 5
```
```output
some 10
```
-/
@[inline, deprecated Iter.findSomeM? (since := "2025-12-04")]
def Iter.Partial.findSomeM? {α β : Type w} {γ : Type x} {m : Type x → Type w'} [Monad m]
    [Iterator α Id β] [IteratorLoop α Id m] (it : Iter.Partial (α := α) β)
    (f : β → m (Option γ)) :
    m (Option γ) :=
  it.it.findSomeM? f

/--
Returns the first non-`none` result of applying the monadic function `f` to each output
of the iterator, in order. Returns `none` if `f` returns `none` for all outputs.

`O(|it|)`. Short-circuits when `f` returns `some _`. The outputs of `it` are
examined in order of iteration.

This variant terminates after finitely many steps and requires a proof that the iterator is
finite. If such a proof is not available, consider using `Iter.findSomeM?`.

Example:
```lean example
#eval [7, 6, 5, 8, 1, 2, 6].iter.findSomeM? fun i => do
  if i < 5 then
    return some (i * 10)
  if i ≤ 6 then
    IO.println s!"Almost! {i}"
  return none
```
```output
Almost! 6
Almost! 5
```
```output
some 10
```
-/
@[inline]
def Iter.Total.findSomeM? {α β : Type w} {γ : Type x} {m : Type x → Type w'} [Monad m]
    [Iterator α Id β] [IteratorLoop α Id m] [Finite α Id] (it : Iter.Total (α := α) β)
    (f : β → m (Option γ)) :
    m (Option γ) :=
  it.it.findSomeM? f

/--
Returns the first non-`none` result of applying `f` to each output of the iterator, in order.
Returns `none` if `f` returns `none` for all outputs.

`O(|it|)`. Short-circuits when `f` returns `some _`.The outputs of `it` are examined in order of
iteration.

If the iterator is not finite, this function might run forever. The variant
`it.ensureTermination.findSome?` always terminates after finitely many steps.

Examples:
 * `[7, 6, 5, 8, 1, 2, 6].iter.findSome? (fun x => if x < 5 then some (10 * x) else none) = some 10`
 * `[7, 6, 5, 8, 1, 2, 6].iter.findSome? (fun x => if x < 1 then some (10 * x) else none) = none`
-/
@[inline]
def Iter.findSome? {α β : Type w} {γ : Type x} [Iterator α Id β]
    [IteratorLoop α Id Id] (it : Iter (α := α) β) (f : β → Option γ) :
    Option γ :=
  Id.run (it.findSomeM? (pure <| f ·))

/--
Returns the first non-`none` result of applying `f` to each output of the iterator, in order.
Returns `none` if `f` returns `none` for all outputs.

`O(|it|)`. Short-circuits when `f` returns `some _`.The outputs of `it` are examined in order of
iteration.

This function is deprecated. Instead of `it.allowNontermination.findSome?`, use `it.findSome?`.

Examples:
 * `[7, 6, 5, 8, 1, 2, 6].iter.allowNontermination.findSome? (fun x => if x < 5 then some (10 * x) else none) = some 10`
 * `[7, 6, 5, 8, 1, 2, 6].iter.allowNontermination.findSome? (fun x => if x < 1 then some (10 * x) else none) = none`
-/
@[inline, deprecated Iter.findSome? (since := "2025-12-04")]
def Iter.Partial.findSome? {α β : Type w} {γ : Type x} [Iterator α Id β]
    [IteratorLoop α Id Id] (it : Iter.Partial (α := α) β) (f : β → Option γ) :
    Option γ :=
  it.it.findSome? f

/--
Returns the first non-`none` result of applying `f` to each output of the iterator, in order.
Returns `none` if `f` returns `none` for all outputs.

`O(|it|)`. Short-circuits when `f` returns `some _`.The outputs of `it` are examined in order of
iteration.

This variant terminates after finitely many steps and requires a proof that the iterator is
finite. If such a proof is not available, consider using `Iter.findSome?`.

Examples:
 * `[7, 6, 5, 8, 1, 2, 6].iter.ensureTermination.findSome? (fun x => if x < 5 then some (10 * x) else none) = some 10`
 * `[7, 6, 5, 8, 1, 2, 6].iter.ensureTermination.findSome? (fun x => if x < 1 then some (10 * x) else none) = none`
-/
@[inline]
def Iter.Total.findSome? {α β : Type w} {γ : Type x} [Iterator α Id β]
    [IteratorLoop α Id Id] [Finite α Id] (it : Iter.Total (α := α) β) (f : β → Option γ) :
    Option γ :=
  it.it.findSome? f

/--
Returns the first output of the iterator for which the monadic predicate `p` returns `true`, or
`none` if no such element is found.

`O(|it|)`. Short-circuits when `f` returns `true`. The outputs of `it` are examined in order of
iteration.

If the iterator is not finite, this function might run forever. The variant
`it.ensureTermination.findM?` always terminates after finitely many steps.

Example:
```lean example
#eval [7, 6, 5, 8, 1, 2, 6].iter.findM? fun i => do
  if i < 5 then
    return true
  if i ≤ 6 then
    IO.println s!"Almost! {i}"
  return false
```
```output
Almost! 6
Almost! 5
```
```output
some 1
```
-/
@[inline]
def Iter.findM? {α β : Type w} {m : Type w → Type w'} [Monad m] [Iterator α Id β]
    [IteratorLoop α Id m] (it : Iter (α := α) β) (f : β → m (ULift Bool)) :
    m (Option β) :=
  it.findSomeM? (fun x => return if (← f x).down then some x else none)

/--
Returns the first output of the iterator for which the monadic predicate `p` returns `true`, or
`none` if no such element is found.

`O(|it|)`. Short-circuits when `f` returns `true`. The outputs of `it` are examined in order of
iteration.

This function is deprecated. Instead of `it.ensureTermination.findM?`, use `it.findM?`.

Example:
```lean example
#eval [7, 6, 5, 8, 1, 2, 6].iter.findM? fun i => do
  if i < 5 then
    return true
  if i ≤ 6 then
    IO.println s!"Almost! {i}"
  return false
```
```output
Almost! 6
Almost! 5
```
```output
some 1
```
-/
@[inline, deprecated Iter.findM? (since := "2025-12-04")]
def Iter.Partial.findM? {α β : Type w} {m : Type w → Type w'} [Monad m] [Iterator α Id β]
    [IteratorLoop α Id m] (it : Iter.Partial (α := α) β) (f : β → m (ULift Bool)) :
    m (Option β) :=
  it.it.findM? f

/--
Returns the first output of the iterator for which the monadic predicate `p` returns `true`, or
`none` if no such element is found.

`O(|it|)`. Short-circuits when `f` returns `true`. The outputs of `it` are examined in order of
iteration.

This variant requires terminates after finitely many steps and requires a proof that the iterator is
finite. If such a proof is not available, consider using `Iter.findM?`.

Example:
```lean example
#eval [7, 6, 5, 8, 1, 2, 6].iter.findM? fun i => do
  if i < 5 then
    return true
  if i ≤ 6 then
    IO.println s!"Almost! {i}"
  return false
```
```output
Almost! 6
Almost! 5
```
```output
some 1
```
-/
@[inline]
def Iter.Total.findM? {α β : Type w} {m : Type w → Type w'} [Monad m] [Iterator α Id β]
    [IteratorLoop α Id m] [Finite α Id] (it : Iter.Total (α := α) β) (f : β → m (ULift Bool)) :
    m (Option β) :=
  it.it.findM? f

/--
Returns the first output of the iterator for which the predicate `p` returns `true`, or `none` if
no such output is found.

`O(|it|)`. Short-circuits upon encountering the first match. The elements in `it` are examined in
order of iteration.

If the iterator is not finite, this function might run forever. The variant
`it.ensureTermination.find?` always terminates after finitely many steps.

Examples:
* `[7, 6, 5, 8, 1, 2, 6].iter.find? (· < 5) = some 1`
* `[7, 6, 5, 8, 1, 2, 6].iter.find? (· < 1) = none`
-/
@[inline]
def Iter.find? {α β : Type w} [Iterator α Id β] [IteratorLoop α Id Id]
    (it : Iter (α := α) β) (f : β → Bool) : Option β :=
  Id.run (it.findM? (pure <| .up <| f ·))

/--
Returns the first output of the iterator for which the predicate `p` returns `true`, or `none` if
no such output is found.

`O(|it|)`. Short-circuits upon encountering the first match. The elements in `it` are examined in
order of iteration.

This function is deprecated. Instead of `it.allowNontermination.find?`, use `it.find?`.

Examples:
* `[7, 6, 5, 8, 1, 2, 6].iter.allowNontermination.find? (· < 5) = some 1`
* `[7, 6, 5, 8, 1, 2, 6].iter.allowNontermination.find? (· < 1) = none`
-/
@[inline, deprecated Iter.find? (since := "2025-12-04")]
def Iter.Partial.find? {α β : Type w} [Iterator α Id β] [IteratorLoop α Id Id]
    (it : Iter.Partial (α := α) β) (f : β → Bool) : Option β :=
  it.it.find? f

/--
Returns the first output of the iterator for which the predicate `p` returns `true`, or `none` if
no such output is found.

`O(|it|)`. Short-circuits upon encountering the first match. The elements in `it` are examined in
order of iteration.

This variant terminates after finitely many steps and requires a proof that the iterator is
finite. If such a proof is not available, consider using `Iter.find?`.

Examples:
* `[7, 6, 5, 8, 1, 2, 6].iter.find? (· < 5) = some 1`
* `[7, 6, 5, 8, 1, 2, 6].iter.find? (· < 1) = none`
-/
@[inline]
def Iter.Total.find? {α β : Type w} [Iterator α Id β] [IteratorLoop α Id Id] [Finite α Id]
    (it : Iter.Total (α := α) β) (f : β → Bool) : Option β :=
  it.it.find? f

/--
Steps through the whole iterator, counting the number of outputs emitted.

**Performance**:

This function's runtime is linear in the number of steps taken by the iterator.
-/
@[always_inline, inline, expose]
def Iter.count {α : Type w} {β : Type w} [Iterator α Id β] [IteratorLoop α Id Id]
    (it : Iter (α := α) β) : Nat :=
  it.toIterM.count.run.down

/--
Steps through the whole iterator, counting the number of outputs emitted.

**Performance**:

This function's runtime is linear in the number of steps taken by the iterator.
-/
@[always_inline, inline, expose, deprecated Iter.count (since := "2025-10-29")]
def Iter.size {α : Type w} {β : Type w} [Iterator α Id β] [IteratorLoop α Id Id]
    (it : Iter (α := α) β) : Nat :=
   it.count

/--
Steps through the whole iterator, counting the number of outputs emitted.

**Performance**:

This function's runtime is linear in the number of steps taken by the iterator.
-/
@[always_inline, inline, expose, deprecated Iter.count (since := "2025-12-04")]
def Iter.Partial.count {α : Type w} {β : Type w} [Iterator α Id β] [IteratorLoop α Id Id]
    (it : Iter.Partial (α := α) β) : Nat :=
  it.it.toIterM.count.run.down

/--
Steps through the whole iterator, counting the number of outputs emitted.

**Performance**:

This function's runtime is linear in the number of steps taken by the iterator.
-/
@[always_inline, inline, expose, deprecated Iter.count (since := "2025-10-29")]
def Iter.Partial.size {α : Type w} {β : Type w} [Iterator α Id β] [IteratorLoop α Id Id]
    (it : Iter.Partial (α := α) β) : Nat :=
  it.it.count

end Std
