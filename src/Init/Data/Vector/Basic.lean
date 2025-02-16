/-
Copyright (c) 2024 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas, François G. Dorais, Kim Morrison
-/

prelude
import Init.Data.Array.Lemmas
import Init.Data.Array.MapIdx
import Init.Data.Array.InsertIdx
import Init.Data.Range
import Init.Data.Stream

/-!
# Vectors

`Vector α n` is a thin wrapper around `Array α` for arrays of fixed size `n`.
-/

/-- `Vector α n` is an `Array α` with size `n`. -/
structure Vector (α : Type u) (n : Nat) extends Array α where
  /-- Array size. -/
  size_toArray : toArray.size = n
deriving Repr, DecidableEq

attribute [simp] Vector.size_toArray

/-- Convert `xs : Array α` to `Vector α xs.size`. -/
abbrev Array.toVector (xs : Array α) : Vector α xs.size := .mk xs rfl

namespace Vector

/-- Syntax for `Vector α n` -/
syntax (name := «term#v[_,]») "#v[" withoutPosition(term,*,?) "]" : term

open Lean in
macro_rules
  | `(#v[ $elems,* ]) => `(Vector.mk (n := $(quote elems.getElems.size)) #[$elems,*] rfl)

recommended_spelling "empty" for "#v[]" in [Vector.mk, «term#v[_,]»]
recommended_spelling "singleton" for "#v[x]" in [Vector.mk, «term#v[_,]»]

/-- Custom eliminator for `Vector α n` through `Array α` -/
@[elab_as_elim]
def elimAsArray {motive : Vector α n → Sort u}
    (mk : ∀ (a : Array α) (ha : a.size = n), motive ⟨a, ha⟩) :
    (v : Vector α n) → motive v
  | ⟨a, ha⟩ => mk a ha

/-- Custom eliminator for `Vector α n` through `List α` -/
@[elab_as_elim]
def elimAsList {motive : Vector α n → Sort u}
    (mk : ∀ (a : List α) (ha : a.length = n), motive ⟨⟨a⟩, ha⟩) :
    (v : Vector α n) → motive v
  | ⟨⟨a⟩, ha⟩ => mk a ha

/-- Make an empty vector with pre-allocated capacity. -/
@[inline] def mkEmpty (capacity : Nat) : Vector α 0 := ⟨.mkEmpty capacity, rfl⟩

/-- Makes a vector of size `n` with all cells containing `v`. -/
@[inline] def mkVector (n) (v : α) : Vector α n := ⟨mkArray n v, by simp⟩

instance : Nonempty (Vector α 0) := ⟨#v[]⟩
instance [Nonempty α] : Nonempty (Vector α n) := ⟨mkVector _ Classical.ofNonempty⟩

/-- Returns a vector of size `1` with element `v`. -/
@[inline] def singleton (v : α) : Vector α 1 := ⟨#[v], rfl⟩

instance [Inhabited α] : Inhabited (Vector α n) where
  default := mkVector n default

/-- Get an element of a vector using a `Fin` index. -/
@[inline] def get (v : Vector α n) (i : Fin n) : α :=
  v.toArray[(i.cast v.size_toArray.symm).1]

/-- Get an element of a vector using a `USize` index and a proof that the index is within bounds. -/
@[inline] def uget (v : Vector α n) (i : USize) (h : i.toNat < n) : α :=
  v.toArray.uget i (v.size_toArray.symm ▸ h)

instance : GetElem (Vector α n) Nat α fun _ i => i < n where
  getElem x i h := get x ⟨i, h⟩

/-- Check if there is an element which satisfies `a == ·`. -/
def contains [BEq α] (v : Vector α n) (a : α) : Bool := v.toArray.contains a

/-- `a ∈ v` is a predicate which asserts that `a` is in the vector `v`. -/
structure Mem (as : Vector α n) (a : α) : Prop where
  val : a ∈ as.toArray

instance : Membership α (Vector α n) where
  mem := Mem

/--
Get an element of a vector using a `Nat` index. Returns the given default value if the index is out
of bounds.
-/
@[inline] def getD (v : Vector α n) (i : Nat) (default : α) : α := v.toArray.getD i default

/-- The last element of a vector. Panics if the vector is empty. -/
@[inline] def back! [Inhabited α] (v : Vector α n) : α := v.toArray.back!

/-- The last element of a vector, or `none` if the vector is empty. -/
@[inline] def back? (v : Vector α n) : Option α := v.toArray.back?

/-- The last element of a non-empty vector. -/
@[inline] def back [NeZero n] (v : Vector α n) : α :=
  v[n - 1]'(Nat.sub_one_lt (NeZero.ne n))

/-- The first element of a non-empty vector.  -/
@[inline] def head [NeZero n] (v : Vector α n) := v[0]'(Nat.pos_of_neZero n)

/-- Push an element `x` to the end of a vector. -/
@[inline] def push (v : Vector α n) (x : α) : Vector α (n + 1) :=
  ⟨v.toArray.push x, by simp⟩

/-- Remove the last element of a vector. -/
@[inline] def pop (v : Vector α n) : Vector α (n - 1) :=
  ⟨Array.pop v.toArray, by simp⟩

/--
Set an element in a vector using a `Nat` index, with a tactic provided proof that the index is in
bounds.

This will perform the update destructively provided that the vector has a reference count of 1.
-/
@[inline] def set (v : Vector α n) (i : Nat) (x : α) (h : i < n := by get_elem_tactic): Vector α n :=
  ⟨v.toArray.set i x (by simp [*]), by simp⟩

/--
Set an element in a vector using a `Nat` index. Returns the vector unchanged if the index is out of
bounds.

This will perform the update destructively provided that the vector has a reference count of 1.
-/
@[inline] def setIfInBounds (v : Vector α n) (i : Nat) (x : α) : Vector α n :=
  ⟨v.toArray.setIfInBounds i x, by simp⟩

/--
Set an element in a vector using a `Nat` index. Panics if the index is out of bounds.

This will perform the update destructively provided that the vector has a reference count of 1.
-/
@[inline] def set! (v : Vector α n) (i : Nat) (x : α) : Vector α n :=
  ⟨v.toArray.set! i x, by simp⟩

@[inline] def foldlM [Monad m] (f : β → α → m β) (b : β) (v : Vector α n) : m β :=
  v.toArray.foldlM f b

@[inline] def foldrM [Monad m] (f : α → β → m β) (b : β) (v : Vector α n) : m β :=
  v.toArray.foldrM f b

@[inline] def foldl (f : β → α → β) (b : β) (v : Vector α n) : β :=
  v.toArray.foldl f b

@[inline] def foldr (f : α → β → β) (b : β) (v : Vector α n) : β :=
  v.toArray.foldr f b

/-- Append two vectors. -/
@[inline] def append (v : Vector α n) (w : Vector α m) : Vector α (n + m) :=
  ⟨v.toArray ++ w.toArray, by simp⟩

instance : HAppend (Vector α n) (Vector α m) (Vector α (n + m)) where
  hAppend := append

/-- Creates a vector from another with a provably equal length. -/
@[inline] protected def cast (h : n = m) (v : Vector α n) : Vector α m :=
  ⟨v.toArray, by simp [*]⟩

/--
Extracts the slice of a vector from indices `start` to `stop` (exclusive). If `start ≥ stop`, the
result is empty. If `stop` is greater than the size of the vector, the size is used instead.
-/
@[inline] def extract (v : Vector α n) (start : Nat := 0) (stop : Nat := n) : Vector α (min stop n - start) :=
  ⟨v.toArray.extract start stop, by simp⟩

/--
Extract the first `m` elements of a vector. If `m` is greater than or equal to the size of the
vector then the vector is returned unchanged.
-/
@[inline] def take (v : Vector α n) (m : Nat) : Vector α (min m n) :=
  ⟨v.toArray.take m, by simp⟩

@[simp] theorem take_eq_extract (v : Vector α n) (m : Nat) : v.take m = v.extract 0 m := rfl

/--
Deletes the first `m` elements of a vector. If `m` is greater than or equal to the size of the
vector then the empty vector is returned.
-/
@[inline] def drop (v : Vector α n) (m : Nat) : Vector α (n - m) :=
  ⟨v.toArray.drop m, by simp⟩

@[simp] theorem drop_eq_cast_extract (v : Vector α n) (m : Nat) :
    v.drop m = (v.extract m n).cast (by simp) := by
  simp [drop, extract, Vector.cast]

/-- Shrinks a vector to the first `m` elements, by repeatedly popping the last element. -/
@[inline] def shrink (v : Vector α n) (m : Nat) : Vector α (min m n) :=
  ⟨v.toArray.shrink m, by simp⟩

@[simp] theorem shrink_eq_take (v : Vector α n) (m : Nat) : v.shrink m = v.take m := by
  simp [shrink, take]

/-- Maps elements of a vector using the function `f`. -/
@[inline] def map (f : α → β) (v : Vector α n) : Vector β n :=
  ⟨v.toArray.map f, by simp⟩

/-- Maps elements of a vector using the function `f`, which also receives the index of the element. -/
@[inline] def mapIdx (f : Nat → α → β) (v : Vector α n) : Vector β n :=
  ⟨v.toArray.mapIdx f, by simp⟩

/-- Maps elements of a vector using the function `f`,
which also receives the index of the element, and the fact that the index is less than the size of the vector. -/
@[inline] def mapFinIdx (v : Vector α n) (f : (i : Nat) → α → (h : i < n) → β) : Vector β n :=
  ⟨v.toArray.mapFinIdx (fun i a h => f i a (by simpa [v.size_toArray] using h)), by simp⟩

/-- Map a monadic function over a vector. -/
@[inline] def mapM [Monad m] (f : α → m β) (v : Vector α n) : m (Vector β n) := do
  go 0 (Nat.zero_le n) #v[]
where
  go (i : Nat) (h : i ≤ n) (r : Vector β i) : m (Vector β n) := do
    if h' : i < n then
      go (i+1) (by omega) (r.push (← f v[i]))
    else
      return r.cast (by omega)

@[inline] protected def forM [Monad m] (v : Vector α n) (f : α → m PUnit) : m PUnit :=
  v.toArray.forM f

@[inline] def flatMapM [Monad m] (v : Vector α n) (f : α → m (Vector β k)) : m (Vector β (n * k)) := do
  go 0 (Nat.zero_le n) (#v[].cast (by omega))
where
  go (i : Nat) (h : i ≤ n) (r : Vector β (i * k)) : m (Vector β (n * k)) := do
    if h' : i < n then
      go (i+1) (by omega) ((r ++ (← f v[i])).cast (Nat.succ_mul i k).symm)
    else
      return r.cast (by congr; omega)

/-- Variant of `mapIdxM` which receives the index `i` along with the bound `i < n. -/
@[inline]
def mapFinIdxM {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m]
    (as : Vector α n) (f : (i : Nat) → α → (h : i < n) → m β) : m (Vector β n) :=
  let rec @[specialize] map (i : Nat) (j : Nat) (inv : i + j = n) (bs : Vector β (n - i)) : m (Vector β n) := do
    match i, inv with
    | 0,    _  => pure bs
    | i+1, inv =>
      have j_lt : j < n := by
        rw [← inv, Nat.add_assoc, Nat.add_comm 1 j, Nat.add_comm]
        apply Nat.le_add_right
      have : i + (j + 1) = n := by rw [← inv, Nat.add_comm j 1, Nat.add_assoc]
      map i (j+1) this ((bs.push (← f j as[j] j_lt)).cast (by omega))
  map n 0 rfl (#v[].cast (by simp))

@[inline]
def mapIdxM {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (f : Nat → α → m β) (as : Vector α n) : m (Vector β n) :=
  as.mapFinIdxM fun i a _ => f i a

@[inline] def firstM {α : Type u} {m : Type v → Type w} [Alternative m] (f : α → m β) (as : Vector α n) : m β :=
  as.toArray.firstM f

@[inline] def flatten (v : Vector (Vector α n) m) : Vector α (m * n) :=
  ⟨(v.toArray.map Vector.toArray).flatten,
    by rcases v; simp_all [Function.comp_def, Array.map_const']⟩

@[inline] def flatMap (v : Vector α n) (f : α → Vector β m) : Vector β (n * m) :=
  ⟨v.toArray.flatMap fun a => (f a).toArray, by simp [Array.map_const']⟩

@[inline] def zipIdx (v : Vector α n) (k : Nat := 0) : Vector (α × Nat) n :=
  ⟨v.toArray.zipIdx k, by simp⟩

@[deprecated zipIdx (since := "2025-01-21")]
abbrev zipWithIndex := @zipIdx

@[inline] def zip (v : Vector α n) (w : Vector β n) : Vector (α × β) n :=
  ⟨v.toArray.zip w.toArray, by simp⟩

/-- Maps corresponding elements of two vectors of equal size using the function `f`. -/
@[inline] def zipWith (f : α → β → φ) (a : Vector α n) (b : Vector β n) : Vector φ n :=
  ⟨Array.zipWith f a.toArray b.toArray, by simp⟩

@[inline] def unzip (v : Vector (α × β) n) : Vector α n × Vector β n :=
  ⟨⟨v.toArray.unzip.1, by simp⟩, ⟨v.toArray.unzip.2, by simp⟩⟩

/-- The vector of length `n` whose `i`-th element is `f i`. -/
@[inline] def ofFn (f : Fin n → α) : Vector α n :=
  ⟨Array.ofFn f, by simp⟩

/--
Swap two elements of a vector using `Fin` indices.

This will perform the update destructively provided that the vector has a reference count of 1.
-/
@[inline] def swap (v : Vector α n) (i j : Nat)
    (hi : i < n := by get_elem_tactic) (hj : j < n := by get_elem_tactic) : Vector α n :=
  ⟨v.toArray.swap i j (by simpa using hi) (by simpa using hj), by simp⟩

/--
Swap two elements of a vector using `Nat` indices. Panics if either index is out of bounds.

This will perform the update destructively provided that the vector has a reference count of 1.
-/
@[inline] def swapIfInBounds (v : Vector α n) (i j : Nat) : Vector α n :=
  ⟨v.toArray.swapIfInBounds i j, by simp⟩

/--
Swaps an element of a vector with a given value using a `Fin` index. The original value is returned
along with the updated vector.

This will perform the update destructively provided that the vector has a reference count of 1.
-/
@[inline] def swapAt (v : Vector α n) (i : Nat) (x : α) (hi : i < n := by get_elem_tactic) :
    α × Vector α n :=
  let a := v.toArray.swapAt i x (by simpa using hi)
  ⟨a.fst, a.snd, by simp [a]⟩

/--
Swaps an element of a vector with a given value using a `Nat` index. Panics if the index is out of
bounds. The original value is returned along with the updated vector.

This will perform the update destructively provided that the vector has a reference count of 1.
-/
@[inline] def swapAt! (v : Vector α n) (i : Nat) (x : α) : α × Vector α n :=
  let a := v.toArray.swapAt! i x
  ⟨a.fst, a.snd, by simp [a]⟩

/-- The vector `#v[0, 1, 2, ..., n-1]`. -/
@[inline] def range (n : Nat) : Vector Nat n := ⟨Array.range n, by simp⟩

/-- The vector `#v[start, start + step, start + 2 * step, ..., start + (size - 1) * step]`. -/
@[inline] def range' (start size : Nat) (step : Nat := 1) : Vector Nat size :=
  ⟨Array.range' start size step, by simp⟩

/--
Compares two vectors of the same size using a given boolean relation `r`. `isEqv v w r` returns
`true` if and only if `r v[i] w[i]` is true for all indices `i`.
-/
@[inline] def isEqv (v w : Vector α n) (r : α → α → Bool) : Bool :=
  Array.isEqvAux v.toArray w.toArray (by simp) r n (by simp)

instance [BEq α] : BEq (Vector α n) where
  beq a b := isEqv a b (· == ·)

/-- Reverse the elements of a vector. -/
@[inline] def reverse (v : Vector α n) : Vector α n :=
  ⟨v.toArray.reverse, by simp⟩

/-- Delete an element of a vector using a `Nat` index and a tactic provided proof. -/
@[inline] def eraseIdx (v : Vector α n) (i : Nat) (h : i < n := by get_elem_tactic) :
    Vector α (n-1) :=
  ⟨v.toArray.eraseIdx i (v.size_toArray.symm ▸ h), by simp [Array.size_eraseIdx]⟩

/-- Delete an element of a vector using a `Nat` index. Panics if the index is out of bounds. -/
@[inline] def eraseIdx! (v : Vector α n) (i : Nat) : Vector α (n-1) :=
  if _ : i < n then
    v.eraseIdx i
  else
    have : Inhabited (Vector α (n-1)) := ⟨v.pop⟩
    panic! "index out of bounds"

/-- Insert an element into a vector using a `Nat` index and a tactic provided proof. -/
@[inline] def insertIdx (v : Vector α n) (i : Nat) (x : α) (h : i ≤ n := by get_elem_tactic) :
    Vector α (n+1) :=
  ⟨v.toArray.insertIdx i x (v.size_toArray.symm ▸ h), by simp [Array.size_insertIdx]⟩

/-- Insert an element into a vector using a `Nat` index. Panics if the index is out of bounds. -/
@[inline] def insertIdx! (v : Vector α n) (i : Nat) (x : α) : Vector α (n+1) :=
  if _ : i ≤ n then
    v.insertIdx i x
  else
    have : Inhabited (Vector α (n+1)) := ⟨v.push x⟩
    panic! "index out of bounds"

/-- Delete the first element of a vector. Returns the empty vector if the input vector is empty. -/
@[inline] def tail (v : Vector α n) : Vector α (n-1) :=
  if _ : 0 < n then
    v.eraseIdx 0
  else
    v.cast (by omega)

/--
Finds the first index of a given value in a vector using `==` for comparison. Returns `none` if the
no element of the index matches the given value.
-/
@[inline] def finIdxOf? [BEq α] (v : Vector α n) (x : α) : Option (Fin n) :=
  (v.toArray.finIdxOf? x).map (Fin.cast v.size_toArray)

@[deprecated finIdxOf? (since := "2025-01-29")]
abbrev indexOf? := @finIdxOf?

/-- Finds the first index of a given value in a vector using a predicate. Returns `none` if the
no element of the index matches the given value. -/
@[inline] def findFinIdx? (p : α → Bool) (v : Vector α n) : Option (Fin n) :=
  (v.toArray.findFinIdx? p).map (Fin.cast v.size_toArray)

/--
Note that the universe level is contrained to `Type` here,
to avoid having to have the predicate live in `p : α → m (ULift Bool)`.
-/
@[inline] def findM? {α : Type} {m : Type → Type} [Monad m] (f : α → m Bool) (as : Vector α n) : m (Option α) :=
  as.toArray.findM? f

@[inline] def findSomeM? [Monad m] (f : α → m (Option β)) (as : Vector α n) : m (Option β) :=
  as.toArray.findSomeM? f

/--
Note that the universe level is contrained to `Type` here,
to avoid having to have the predicate live in `p : α → m (ULift Bool)`.
-/
@[inline] def findRevM? {α : Type} {m : Type → Type} [Monad m] (f : α → m Bool) (as : Vector α n) : m (Option α) :=
  as.toArray.findRevM? f

@[inline] def findSomeRevM? [Monad m] (f : α → m (Option β)) (as : Vector α n) : m (Option β) :=
  as.toArray.findSomeRevM? f

@[inline] def find? {α : Type} (f : α → Bool) (as : Vector α n) : Option α :=
  as.toArray.find? f

@[inline] def findRev? {α : Type} (f : α → Bool) (as : Vector α n) : Option α :=
  as.toArray.findRev? f

@[inline] def findSome? (f : α → Option β) (as : Vector α n) : Option β :=
  as.toArray.findSome? f

@[inline] def findSomeRev? (f : α → Option β) (as : Vector α n) : Option β :=
  as.toArray.findSomeRev? f

/-- Returns `true` when `v` is a prefix of the vector `w`. -/
@[inline] def isPrefixOf [BEq α] (v : Vector α m) (w : Vector α n) : Bool :=
  v.toArray.isPrefixOf w.toArray

/-- Returns `true` with the monad if `p` returns `true` for any element of the vector. -/
@[inline] def anyM [Monad m] (p : α → m Bool) (v : Vector α n) : m Bool :=
  v.toArray.anyM p

/-- Returns `true` with the monad if `p` returns `true` for all elements of the vector. -/
@[inline] def allM [Monad m] (p : α → m Bool) (v : Vector α n) : m Bool :=
  v.toArray.allM p

/-- Returns `true` if `p` returns `true` for any element of the vector. -/
@[inline] def any (v : Vector α n) (p : α → Bool) : Bool :=
  v.toArray.any p

/-- Returns `true` if `p` returns `true` for all elements of the vector. -/
@[inline] def all (v : Vector α n) (p : α → Bool) : Bool :=
  v.toArray.all p

/-- Count the number of elements of a vector that satisfy the predicate `p`. -/
@[inline] def countP (p : α → Bool) (v : Vector α n) : Nat :=
  v.toArray.countP p

/-- Count the number of elements of a vector that are equal to `a`. -/
@[inline] def count [BEq α] (a : α) (v : Vector α n) : Nat :=
  v.toArray.count a

/-! ### ForIn instance -/

@[simp] theorem mem_toArray_iff (a : α) (v : Vector α n) : a ∈ v.toArray ↔ a ∈ v :=
  ⟨fun h => ⟨h⟩, fun ⟨h⟩ => h⟩

instance : ForIn' m (Vector α n) α inferInstance where
  forIn' v b f := Array.forIn' v.toArray b (fun a h b => f a (by simpa using h) b)

/-! ### ForM instance -/

instance : ForM m (Vector α n) α where
  forM := Vector.forM

-- We simplify `Vector.forM` to `forM`.
@[simp] theorem forM_eq_forM [Monad m] (f : α → m PUnit) :
    Vector.forM v f = forM v f := rfl

/-! ### ToStream instance -/

instance : ToStream (Vector α n) (Subarray α) where
  toStream v := v.toArray[:n]

/-! ### Lexicographic ordering -/

instance instLT [LT α] : LT (Vector α n) := ⟨fun v w => v.toArray < w.toArray⟩
instance instLE [LT α] : LE (Vector α n) := ⟨fun v w => v.toArray ≤ w.toArray⟩

/--
Lexicographic comparator for vectors.

`lex v w lt` is true if
- `v` is pairwise equivalent via `==` to `w`, or
- there is an index `i` such that `lt v[i] w[i]`, and for all `j < i`, `v[j] == w[j]`.
-/
def lex [BEq α] (v w : Vector α n) (lt : α → α → Bool := by exact (· < ·)) : Bool := Id.run do
  for h : i in [0 : n] do
    if lt v[i] w[i] then
      return true
    else if v[i] != w[i] then
      return false
  return false
