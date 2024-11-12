/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro, Markus Himmel
-/
prelude
import Init.Data.Array.Lemmas
import Std.Data.DHashMap.RawDef
import Std.Data.DHashMap.Internal.List.Defs
import Std.Data.DHashMap.Internal.Index

/-!
This is an internal implementation file of the hash map. Users of the hash map should not rely on
the contents of this file.

File contents: Definition of all operations on `Raw₀`, definition of `WFImp`.

# Hash map implementation notes

This is a simple separate-chaining hash table. The data of the hash map (`DHashMap.Raw`) consists of
a cached size and an array of buckets, where each bucket is an `AssocList α β` (which is the same as
a `List ((a : α) × β a)` but with one less level of indirection). The number of buckets is always a
power of two. The hash map doubles its size upon inserting an element such that the number of
elements is more than 75% of the number of buckets.

Because we need `DHashMap.Raw` to be nested-inductive-safe, we cannot bundle the fact that there is
at least one bucket. We there for define a type `Raw₀` which is just a `Raw` together with the fact
that the size is positive. Almost all internal work on the hash map happens on `Raw₀` so that we do
not have to perform size check all of the time. The operations defined on `Raw` perform this size
check once to transform the `Raw` into a `Raw₀` and then operate on that (therefore, each operation
on `Raw` will only do a single size check). The operations defined on `DHashMap` conclude that the
size is positive from the well-formedness predicate, use that to build a `Raw₀` and then operate on
that. So the operations on `DHashMap` are exactly the same as the operations on `Raw₀` and the
operations on `Raw` are the same as the operations on `Raw₀` as long as we can prove that the size
check will succeed.

The operations on `Raw₀` are defined in this file. They are built for performance. The IR is
hand-checked to ensure that there are no unnecessary allocations, inlining problems or linearity
bugs. Note that for many operations the IR only becomes meaningful once it has been specialized with
concrete `Hashable` and `BEq` instances as is the case in actual applications.

Of the internal files, only `Internal.Index`, `Internal.Defs` and `Internal.AssocList.Basic` contain
any executable code. The rest of the files set up the verification framework which is described in
the remainder of this text.

The basic idea is to translate statements about hash maps into statements about lists using the
function `toListModel` defined in this file. The function `toListModel` simply concatenates all
buckets into a `List ((a : α) × β a)`. The file `Internal.List.Associative` then contains a complete
verification of associative lists. The theorems relating the operations on `Raw₀` to the operations
on `List ((a : α) × β a)` are located in `Internal.WF` and have such names as
`contains_eq_containsKey` or `toListModel_insert`. In the file `Internal.RawLemmas` we then state
all of the lemmas for `Raw₀` and use a tactic to apply the results from `Internal.WF` to reduce to
the results from `Internal.List.Associative`. From there we can state the actual lemmas for
`DHashMap.Raw`, `DHashMap`, `HashMap.Raw`, `HashMap`, `HashSet.Raw` and `HashSet` in the
non-internal `*.Lemmas` files and immediately reduce them to the results about `Raw₀` in
`Internal.RawLemmas`.

There are some additional indirections to this high-level strategy. First, we have an additional
layer of so-called "model functions" on `Raw₀`, defined in the file `Internal.Model`. These have the
same signature as their counterparts defined in this file, but may have a slightly simpler
implementation. For example, `Raw₀.erase` has a linearity optimization which is not present in the
model function `Raw₀.eraseₘ`. We prove that the functions are equal to their model implementations
in `Internal.Model`, then verify the model implementation. This makes the verification more robust
against implementation details, future performance improvements, etc.

Second, reducing hash maps to lists only works if the hash map is well-formed. Our internal
well-formedness predicate is called `Raw.WFImp` (defined in this file) and states that (a) each
bucket only contains items with the correct hash, (b) the cached size is equal to the actual number
of elements in the buckets, and (c) after concatenating the buckets the keys in the resulting list
are pairwise not equal. The third condition is a priori stronger than the slightly more natural
condition that the keys in each bucket are pairwise not equal, but they are equivalent in
well-behaved cases and our condition works better. The user-visible well-formedness predicate
`Raw.WF` is equivalent to `WFImp`, as is shown in `Internal.WF`. The user-visible version exists to
postpone the proofs that all operations preserve well-formedness to a later file so that it is
possible to import `DHashMap.Basic` without pulling in all of the proof machinery.

The framework works very hard to make adding and verifying new operations very easy and
maintainable. To this end, we provide theorems `apply_bucket`, `apply_bucket_with_proof`,
`toListModel_updateBucket` and `toListModel_updateAllBuckets`, which do all of the heavy lifting in
a general way. The verification for each actual operation in `Internal.WF` is then extremely
straightward, requiring only to plug in some results about lists. See for example the functions
`containsₘ_eq_containsKey` and the section on `eraseₘ` for prototypical examples of this technique.

Here is a summary of the steps required to add and verify a new operation:
1. Write the executable implementation
  * Implement the operation `AssocList.operation` on associative lists in `Internal.AssocList.Basic`
  * Implement the operation `Raw₀.operation` on `Raw₀` in `Internal.Defs`
  * Implement the operation `Raw.operation`/`DHashMap.operation` on `DHashMap.Raw` and `DHashMap` in
    `DHashMap.Basic`.
    If your operation modifies the hash map, this will involve adding a new constructor `operation₀`
    to `Raw.WF`. In that case, don't forget to provide a well-formedness lemma `Raw.WF.operation`
    (which differs from `Raw.WF.operation₀` in that it is about the operation on `Raw`, not on
    `Raw₀` (remember, these differ by a bounds check)).
  * Implement the operation `Raw.operation`/`HashMap.operation` on `HashMap.Raw` and `HashMap` in
    `HashMap.Basic`.
  * Implement the operation `Raw.operation`/`HashSet.operation` on `HashSet.Raw` and `HashSet` in
    `HashSet.Basic`
2. Write the list implementation
  * Implement the operation `List.operation` on lists in `Internal.List.Associative`
  * Connect the implementation on lists and associative lists in `Internal.AssocList.Lemmas` via a
    lemma `AssocList.operation_eq`.
3. Write the model implementation
  * Write the model implementation `Raw₀.operationₘ` in `Internal.Model`
  * Prove that the model implementation is equal to the actual implementation in
    `Internal.Model` via a lemma `operation_eq_operationₘ`.
4. Verify the model implementation
  * In `Internal.WF`, prove `operationₘ_eq_List.operation` (for access operations) or
    `wfImp_operationₘ` and `toListModel_operationₘ`
  * Immediately deduce the corresponding results `operation_eq_List.operation` or
    `wfImp_operation`/`toListModel_operation` by combining the results from steps 3 and 4.
  * If you added a new constructor to `Raw.WF` earlier, fix up the proof of `Raw.WF.out`.
5. Connect `Raw` and `Raw₀`
  * Write `Raw.operation_eq` and `Raw.operation_val` in `Internal.Raw`.
6. Prove `Raw₀` versions of user-facing lemmas
  * State all of the user-facing lemmas that you want in `Internal.RawLemmas`. This will generally
    involve connecting the operation to ALL existing operations or deciding that there is nothing to
    be said about a certain pair.
  * Prove the corresponding results about lists in `List.Associative`
  * Use the tactic provided in `Internal.RawLemmas` to deduce the `Raw₀` results from the list
    results. You will need to hook some of the results you proved in step 4 into the tactic. You
    might also have to prove that your list operation is invariant under permutation and add that to
    the tactic.
7. State and prove the user-facing lemmas
  * Restate all of your lemmas for `DHashMap.Raw` in `DHashMap.RawLemmas` and prove them using the
    provided tactic after hooking in your `operation_eq` and `operation_val` from step 5.
  * Restate all of your lemmas for `DHashMap` in `DHashMap.Lemmas` and prove them by reducing to
    `Raw₀`.
  * Restate all of your lemmas for `HashMap.Raw` in `HashMap.RawLemmas` and prove them by reducing to
    `DHashMap.Raw`.
  * Restate all of your lemmas for `HashMap` in `HashMap.Lemmas` and prove them by reducing to
    `DHashMap`.
  * Restate all of your lemmas for `HashSet.Raw` in `HashSet.RawLemmas` and prove them by reducing to
    `HashMap.Raw`.
  * Restate all of your lemmas for `HashSet` in `HashSet.Lemmas` and prove them by reducing to
    `HashMap`.

This sounds like a lot of work (and it is if you have to add a lot of user-facing lemmas), but the
framework is set up in such a way that each step is really easy and the proofs are all really short
and clean.
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v w

variable {α : Type u} {β : α → Type v} {δ : Type w} {m : Type w → Type w} [Monad m]

namespace Std

namespace DHashMap.Internal

@[inline] private def numBucketsForCapacity (capacity : Nat) : Nat :=
  -- a "load factor" of 0.75 is the usual standard for hash maps
  capacity * 4 / 3

/-- Internal implementation detail of the hash map -/
def toListModel (buckets : Array (AssocList α β)) : List ((a : α) × β a) :=
  buckets.toList.flatMap AssocList.toList

/-- Internal implementation detail of the hash map -/
@[inline] def computeSize (buckets : Array (AssocList α β)) : Nat :=
  buckets.foldl (fun d b => d + b.length) 0

/-- Internal implementation detail of the hash map -/
abbrev Raw₀ (α : Type u) (β : α → Type v) :=
  { m : Raw α β // 0 < m.buckets.size }

namespace Raw₀

/-- Internal implementation detail of the hash map -/
@[inline] def empty (capacity := 8) : Raw₀ α β :=
  ⟨⟨0, mkArray (numBucketsForCapacity capacity).nextPowerOfTwo AssocList.nil⟩,
    by simpa using Nat.pos_of_isPowerOfTwo (Nat.isPowerOfTwo_nextPowerOfTwo _)⟩

-- Take `hash` as a function instead of `Hashable α` as per
-- https://github.com/leanprover/lean4/issues/4191
/-- Internal implementation detail of the hash map -/
@[inline] def reinsertAux (hash : α → UInt64) (data : { d : Array (AssocList α β) // 0 < d.size })
    (a : α) (b : β a) : { d : Array (AssocList α β) // 0 < d.size } :=
  let ⟨data, hd⟩ := data
  let ⟨i, h⟩ := mkIdx data.size hd (hash a)
  ⟨data.uset i (data[i].cons a b) h, by simpa⟩

/-- Copies all the entries from `buckets` into a new hash map with a larger capacity. -/
def expand [Hashable α] (data : { d : Array (AssocList α β) // 0 < d.size }) :
    { d : Array (AssocList α β) // 0 < d.size } :=
  let ⟨data, hd⟩ := data
  let nbuckets := data.size * 2
  go 0 data ⟨mkArray nbuckets AssocList.nil, by simpa [nbuckets] using Nat.mul_pos hd Nat.two_pos⟩
where
  /-- Inner loop of `expand`. Copies elements `source[i:]` into `target`,
  destroying `source` in the process. -/
  go (i : Nat) (source : Array (AssocList α β))
      (target : { d : Array (AssocList α β) // 0 < d.size }) :
      { d : Array (AssocList α β) // 0 < d.size } :=
    if h : i < source.size then
      let es := source[i]
      -- We erase `es` from `source` to make sure we can reuse its memory cells
      -- when performing es.foldl
      let source := source.set i .nil
      let target := es.foldl (reinsertAux hash) target
      go (i+1) source target
    else target
  termination_by source.size - i

/-- Internal implementation detail of the hash map -/
@[inline] def expandIfNecessary [BEq α] [Hashable α] (m : Raw₀ α β) : Raw₀ α β :=
  let ⟨⟨size, buckets⟩, hm⟩ := m
  if numBucketsForCapacity size ≤ buckets.size then
    ⟨⟨size, buckets⟩, hm⟩
  else
    let ⟨buckets', h'⟩ := expand ⟨buckets, by simpa⟩
    ⟨⟨size, buckets'⟩, h'⟩

/-- Internal implementation detail of the hash map -/
@[inline] def insert [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) : Raw₀ α β :=
  let ⟨⟨size, buckets⟩, hm⟩ := m
  let ⟨i, h⟩ := mkIdx buckets.size hm (hash a)
  let bkt := buckets[i]
  if bkt.contains a then
    let buckets' := buckets.uset i .nil h
    ⟨⟨size, buckets'.uset i (bkt.replace a b) (by simpa [buckets'])⟩, by simpa [buckets']⟩
  else
    let size'    := size + 1
    let buckets' := buckets.uset i (AssocList.cons a b bkt) h
    expandIfNecessary ⟨⟨size', buckets'⟩, by simpa [buckets']⟩

/-- Internal implementation detail of the hash map -/
@[inline] def containsThenInsert [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) :
    Bool × Raw₀ α β :=
  let ⟨⟨size, buckets⟩, hm⟩ := m
  let ⟨i, h⟩ := mkIdx buckets.size hm (hash a)
  let bkt := buckets[i]
  if bkt.contains a then
    let buckets' := buckets.uset i .nil h
    (true, ⟨⟨size, buckets'.uset i (bkt.replace a b) (by simpa [buckets'])⟩, by simpa [buckets']⟩)
  else
    let size'    := size + 1
    let buckets' := buckets.uset i (AssocList.cons a b bkt) h
    (false, expandIfNecessary ⟨⟨size', buckets'⟩, by simpa [buckets']⟩)

/-- Internal implementation detail of the hash map -/
@[inline] def containsThenInsertIfNew [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) :
    Bool × Raw₀ α β :=
  let ⟨⟨size, buckets⟩, hm⟩ := m
  let ⟨i, h⟩ := mkIdx buckets.size hm (hash a)
  let bkt := buckets[i]
  if bkt.contains a then
    (true, ⟨⟨size, buckets⟩, hm⟩)
  else
    let size'    := size + 1
    let buckets' := buckets.uset i (AssocList.cons a b bkt) h
    (false, expandIfNecessary ⟨⟨size', buckets'⟩, by simpa [buckets']⟩)

/-- Internal implementation detail of the hash map -/
@[inline] def insertIfNew [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) : Raw₀ α β :=
  let ⟨⟨size, buckets⟩, hm⟩ := m
  let ⟨i, h⟩ := mkIdx buckets.size hm (hash a)
  let bkt := buckets[i]
  if bkt.contains a then
    ⟨⟨size, buckets⟩, hm⟩
  else
    let size'    := size + 1
    let buckets' := buckets.uset i (AssocList.cons a b bkt) h
    expandIfNecessary ⟨⟨size', buckets'⟩, by simpa [buckets']⟩

/-- Internal implementation detail of the hash map -/
@[inline] def getThenInsertIfNew? [BEq α] [Hashable α] [LawfulBEq α] (m : Raw₀ α β) (a : α)
    (b : β a) : Option (β a) × Raw₀ α β :=
  let ⟨⟨size, buckets⟩, hm⟩ := m
  let ⟨i, h⟩ := mkIdx buckets.size hm (hash a)
  let bkt := buckets[i]
  match bkt.getCast? a with
  | none =>
    let size'    := size + 1
    let buckets' := buckets.uset i (AssocList.cons a b bkt) h
    (none, expandIfNecessary ⟨⟨size', buckets'⟩, by simpa [buckets']⟩)
  | some v => (some v, ⟨⟨size, buckets⟩, hm⟩)

/-- Internal implementation detail of the hash map -/
@[inline] def get? [BEq α] [LawfulBEq α] [Hashable α] (m : Raw₀ α β) (a : α) : Option (β a) :=
  let ⟨⟨_, buckets⟩, h⟩ := m
  let ⟨i, h⟩ := mkIdx buckets.size h (hash a)
  buckets[i].getCast? a

/-- Internal implementation detail of the hash map -/
@[inline] def contains [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) : Bool :=
  let ⟨⟨_, buckets⟩, h⟩ := m
  let ⟨i, h⟩ := mkIdx buckets.size h (hash a)
  buckets[i].contains a

/-- Internal implementation detail of the hash map -/
@[inline] def get [BEq α] [LawfulBEq α] [Hashable α] (m : Raw₀ α β) (a : α) (hma : m.contains a) :
    β a :=
  let ⟨⟨_, buckets⟩, h⟩ := m
  let idx := mkIdx buckets.size h (hash a)
  buckets[idx.1].getCast a hma

/-- Internal implementation detail of the hash map -/
@[inline] def getD [BEq α] [LawfulBEq α] [Hashable α] (m : Raw₀ α β) (a : α) (fallback : β a) :
    β a :=
  let ⟨⟨_, buckets⟩, h⟩ := m
  let idx := mkIdx buckets.size h (hash a)
  buckets[idx.1].getCastD a fallback

/-- Internal implementation detail of the hash map -/
@[inline] def get! [BEq α] [LawfulBEq α] [Hashable α] (m : Raw₀ α β) (a : α) [Inhabited (β a)] :
    β a :=
  let ⟨⟨_, buckets⟩, h⟩ := m
  let idx := mkIdx buckets.size h (hash a)
  buckets[idx.1].getCast! a

/-- Internal implementation detail of the hash map -/
@[inline] def erase [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) : Raw₀ α β :=
  let ⟨⟨size, buckets⟩, hb⟩ := m
  let ⟨i, h⟩ := mkIdx buckets.size hb (hash a)
  let bkt := buckets[i]
  if bkt.contains a then
    let buckets' := buckets.uset i .nil h
    ⟨⟨size - 1, buckets'.uset i (bkt.erase a) (by simpa [buckets'])⟩, by simpa [buckets']⟩
  else
    ⟨⟨size, buckets⟩, hb⟩

-- Computing the size after the fact was determined to be faster than computing it inline
/-- Internal implementation detail of the hash map -/
@[inline] def filterMap {γ : α → Type w} (f : (a : α) → β a → Option (γ a))
    (m : Raw₀ α β) : Raw₀ α γ :=
  let ⟨⟨_, buckets⟩, hb⟩ := m
  let newBuckets := buckets.map (AssocList.filterMap f)
  ⟨⟨computeSize newBuckets, newBuckets⟩, by simpa [newBuckets] using hb⟩

/-- Internal implementation detail of the hash map -/
@[inline] def map {γ : α → Type w} (f : (a : α) → β a → γ a) (m : Raw₀ α β) : Raw₀ α γ :=
  let ⟨⟨size, buckets⟩, hb⟩ := m
  let newBuckets := buckets.map (AssocList.map f)
  ⟨⟨size, newBuckets⟩, by simpa [newBuckets] using hb⟩

/-- Internal implementation detail of the hash map -/
@[inline] def filter (f : (a : α) → β a → Bool) (m : Raw₀ α β) : Raw₀ α β :=
  let ⟨⟨_, buckets⟩, hb⟩ := m
  let newBuckets := buckets.map (AssocList.filter f)
  ⟨⟨computeSize newBuckets, newBuckets⟩, by simpa [newBuckets] using hb⟩

/-- Internal implementation detail of the hash map -/
@[inline] def insertMany {ρ : Type w} [ForIn Id ρ ((a : α) × β a)] [BEq α] [Hashable α]
    (m : Raw₀ α β) (l : ρ) : { m' : Raw₀ α β // ∀ (P : Raw₀ α β → Prop),
      (∀ {m'' a b}, P m'' → P (m''.insert a b)) → P m → P m' } := Id.run do
  let mut r : { m' : Raw₀ α β // ∀ (P : Raw₀ α β → Prop),
    (∀ {m'' a b}, P m'' → P (m''.insert a b)) → P m → P m' } := ⟨m, fun _ _ => id⟩
  for ⟨a, b⟩ in l do
    r := ⟨r.1.insert a b, fun _ h hm => h (r.2 _ h hm)⟩
  return r

section

variable {β : Type v}

/-- Internal implementation detail of the hash map -/
@[inline] def Const.get? [BEq α] [Hashable α] (m : Raw₀ α (fun _ => β)) (a : α) : Option β :=
  let ⟨⟨_, buckets⟩, h⟩ := m
  let ⟨i, h⟩ := mkIdx buckets.size h (hash a)
  buckets[i].get? a

/-- Internal implementation detail of the hash map -/
@[inline] def Const.get [BEq α] [Hashable α] (m : Raw₀ α (fun _ => β)) (a : α)
    (hma : m.contains a) : β :=
  let ⟨⟨_, buckets⟩, h⟩ := m
  let idx := mkIdx buckets.size h (hash a)
  buckets[idx.1].get a hma

/-- Internal implementation detail of the hash map -/
@[inline] def Const.getD [BEq α] [Hashable α] (m : Raw₀ α (fun _ => β)) (a : α) (fallback : β) :
    β :=
  let ⟨⟨_, buckets⟩, h⟩ := m
  let idx := mkIdx buckets.size h (hash a)
  buckets[idx.1].getD a fallback

/-- Internal implementation detail of the hash map -/
@[inline] def Const.get! [BEq α] [Hashable α] [Inhabited β] (m : Raw₀ α (fun _ => β)) (a : α) : β :=
  let ⟨⟨_, buckets⟩, h⟩ := m
  let idx := mkIdx buckets.size h (hash a)
  buckets[idx.1].get! a

/-- Internal implementation detail of the hash map -/
@[inline] def Const.getThenInsertIfNew? [BEq α] [Hashable α] (m : Raw₀ α (fun _ => β)) (a : α)
    (b : β) : Option β × Raw₀ α (fun _ => β) :=
  let ⟨⟨size, buckets⟩, hm⟩ := m
  let ⟨i, h⟩ := mkIdx buckets.size hm (hash a)
  let bkt := buckets[i]
  match bkt.get? a with
  | none =>
    let size'    := size + 1
    let buckets' := buckets.uset i (AssocList.cons a b bkt) h
    (none, expandIfNecessary ⟨⟨size', buckets'⟩, by simpa [buckets']⟩)
  | some v => (some v, ⟨⟨size, buckets⟩, hm⟩)

/-- Internal implementation detail of the hash map -/
@[inline] def Const.insertMany {ρ : Type w} [ForIn Id ρ (α × β)] [BEq α] [Hashable α]
    (m : Raw₀ α (fun _ => β)) (l : ρ) :
    { m' : Raw₀ α (fun _ => β) // ∀ (P : Raw₀ α (fun _ => β) → Prop),
      (∀ {m'' a b}, P m'' → P (m''.insert a b)) → P m → P m' } := Id.run do
  let mut r : { m' : Raw₀ α (fun _ => β) // ∀ (P : Raw₀ α (fun _ => β) → Prop),
    (∀ {m'' a b}, P m'' → P (m''.insert a b)) → P m → P m' } := ⟨m, fun _ _ => id⟩
  for (a, b) in l do
    r := ⟨r.1.insert a b, fun _ h hm => h (r.2 _ h hm)⟩
  return r

/-- Internal implementation detail of the hash map -/
@[inline] def Const.insertManyUnit {ρ : Type w} [ForIn Id ρ α] [BEq α] [Hashable α]
    (m : Raw₀ α (fun _ => Unit)) (l : ρ) :
    { m' : Raw₀ α (fun _ => Unit) // ∀ (P : Raw₀ α (fun _ => Unit) → Prop),
      (∀ {m'' a b}, P m'' → P (m''.insert a b)) → P m → P m' } := Id.run do
  let mut r : { m' : Raw₀ α (fun _ => Unit) // ∀ (P : Raw₀ α (fun _ => Unit) → Prop),
    (∀ {m'' a b}, P m'' → P (m''.insert a b)) → P m → P m' } := ⟨m, fun _ _ => id⟩
  for a in l do
    r := ⟨r.1.insert a (), fun _ h hm => h (r.2 _ h hm)⟩
  return r

end

/-- Internal implementation detail of the hash map -/
@[inline] def getKey? [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) : Option α :=
  let ⟨⟨_, buckets⟩, h⟩ := m
  let ⟨i, h⟩ := mkIdx buckets.size h (hash a)
  buckets[i].getKey? a

/-- Internal implementation detail of the hash map -/
@[inline] def getKey [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (hma : m.contains a) : α :=
  let ⟨⟨_, buckets⟩, h⟩ := m
  let idx := mkIdx buckets.size h (hash a)
  buckets[idx.1].getKey a hma

/-- Internal implementation detail of the hash map -/
@[inline] def getKeyD [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (fallback : α) : α :=
  let ⟨⟨_, buckets⟩, h⟩ := m
  let idx := mkIdx buckets.size h (hash a)
  buckets[idx.1].getKeyD a fallback

/-- Internal implementation detail of the hash map -/
@[inline] def getKey! [BEq α] [Hashable α] [Inhabited α] (m : Raw₀ α β) (a : α) : α :=
  let ⟨⟨_, buckets⟩, h⟩ := m
  let idx := mkIdx buckets.size h (hash a)
  buckets[idx.1].getKey! a

end Raw₀

/-- Internal implementation detail of the hash map -/
structure List.HashesTo [BEq α] [Hashable α] (l : List ((a : α) × β a)) (i : Nat)
    (size : Nat) : Prop where
  /-- Internal implementation detail of the hash map -/
  hash_self : (h : 0 < size) → ∀ p, p ∈ l → (mkIdx size h (hash p.1)).1.toNat = i

/-- Internal implementation detail of the hash map -/
structure IsHashSelf [BEq α] [Hashable α] (m : Array (AssocList α β)) : Prop where
  /-- Internal implementation detail of the hash map -/
  hashes_to (i : Nat) (h : i < m.size) : List.HashesTo m[i].toList i m.size

namespace Raw

/-- This is the actual well-formedness predicate for hash maps. Users should never need to interact
with this and should use `WF` instead. -/
structure WFImp [BEq α] [Hashable α] (m : Raw α β) : Prop where
  /-- Internal implementation detail of the hash map -/
  buckets_hash_self : IsHashSelf m.buckets
  /-- Internal implementation detail of the hash map -/
  size_eq : m.size = (toListModel m.buckets).length
  /-- Internal implementation detail of the hash map -/
  distinct : List.DistinctKeys (toListModel m.buckets)

end Raw

end Std.DHashMap.Internal
