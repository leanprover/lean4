/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Fin.Basic
import Init.Data.UInt.BasicAux
import Init.Data.Repr
import Init.Data.ToString.Basic
import Init.GetElem
import Init.Data.List.ToArrayImpl
import Init.Data.Array.Set

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

universe u v w

/-! ### Array literal syntax -/

/-- Syntax for `Array α`. -/
syntax (name := «term#[_,]») "#[" withoutPosition(term,*,?) "]" : term

macro_rules
  | `(#[ $elems,* ]) => `(List.toArray [ $elems,* ])

recommended_spelling "empty" for "#[]" in [«term#[_,]»]
recommended_spelling "singleton" for "#[x]" in [«term#[_,]»]

variable {α : Type u}

namespace Array

@[deprecated toList (since := "2024-09-10")] abbrev data := @toList

/-! ### Preliminary theorems -/

@[simp] theorem size_set {xs : Array α} {i : Nat} {v : α} (h : i < xs.size) :
    (set xs i v h).size = xs.size :=
  List.length_set ..

@[simp] theorem size_push {xs : Array α} (v : α) : (push xs v).size = xs.size + 1 :=
  List.length_concat ..

theorem ext {xs ys : Array α}
    (h₁ : xs.size = ys.size)
    (h₂ : (i : Nat) → (hi₁ : i < xs.size) → (hi₂ : i < ys.size) → xs[i] = ys[i])
    : xs = ys := by
  let rec extAux (as bs : List α)
      (h₁ : as.length = bs.length)
      (h₂ : (i : Nat) → (hi₁ : i < as.length) → (hi₂ : i < bs.length) → as[i] = bs[i])
      : as = bs := by
    induction as generalizing bs with
    | nil =>
      cases bs with
      | nil       => rfl
      | cons b bs => rw [List.length_cons] at h₁; injection h₁
    | cons a as ih =>
      cases bs with
      | nil => rw [List.length_cons] at h₁; injection h₁
      | cons b bs =>
        have hz₁ : 0 < (a::as).length := by rw [List.length_cons]; apply Nat.zero_lt_succ
        have hz₂ : 0 < (b::bs).length := by rw [List.length_cons]; apply Nat.zero_lt_succ
        have headEq : a = b := h₂ 0 hz₁ hz₂
        have h₁' : as.length = bs.length := by rw [List.length_cons, List.length_cons] at h₁; injection h₁
        have h₂' : (i : Nat) → (hi₁ : i < as.length) → (hi₂ : i < bs.length) → as[i] = bs[i] := by
          intro i hi₁ hi₂
          have hi₁' : i+1 < (a::as).length := by rw [List.length_cons]; apply Nat.succ_lt_succ; assumption
          have hi₂' : i+1 < (b::bs).length := by rw [List.length_cons]; apply Nat.succ_lt_succ; assumption
          have : (a::as)[i+1] = (b::bs)[i+1] := h₂ (i+1) hi₁' hi₂'
          apply this
        have tailEq : as = bs := ih bs h₁' h₂'
        rw [headEq, tailEq]
  cases xs; cases ys
  apply congrArg
  apply extAux
  assumption
  assumption

theorem ext' {xs ys : Array α} (h : xs.toList = ys.toList) : xs = ys := by
  cases xs; cases ys; simp at h; rw [h]

@[simp] theorem toArrayAux_eq {as : List α} {acc : Array α} : (as.toArrayAux acc).toList = acc.toList ++ as := by
  induction as generalizing acc <;> simp [*, List.toArrayAux, Array.push, List.append_assoc, List.concat_eq_append]

@[simp] theorem toArray_toList {xs : Array α} : xs.toList.toArray = xs := rfl

@[simp] theorem getElem_toList {xs : Array α} {i : Nat} (h : i < xs.size) : xs.toList[i] = xs[i] := rfl

@[simp] theorem getElem?_toList {xs : Array α} {i : Nat} : xs.toList[i]? = xs[i]? := by
  simp [getElem?_def]

/-- `a ∈ as` is a predicate which asserts that `a` is in the array `as`. -/
-- NB: This is defined as a structure rather than a plain def so that a lemma
-- like `sizeOf_lt_of_mem` will not apply with no actual arrays around.
structure Mem (as : Array α) (a : α) : Prop where
  val : a ∈ as.toList

instance : Membership α (Array α) where
  mem := Mem

theorem mem_def {a : α} {as : Array α} : a ∈ as ↔ a ∈ as.toList :=
  ⟨fun | .mk h => h, Array.Mem.mk⟩

@[simp] theorem mem_toArray {a : α} {l : List α} : a ∈ l.toArray ↔ a ∈ l := by
  simp [mem_def]

@[simp] theorem getElem_mem {xs : Array α} {i : Nat} (h : i < xs.size) : xs[i] ∈ xs := by
  rw [Array.mem_def, ← getElem_toList]
  apply List.getElem_mem

end Array

namespace List

@[deprecated Array.toArray_toList (since := "2025-02-17")]
abbrev toArray_toList := @Array.toArray_toList

-- This does not need to be a simp lemma, as already after the `whnfR` the right hand side is `as`.
theorem toList_toArray {as : List α} : as.toArray.toList = as := rfl

@[deprecated toList_toArray (since := "2025-02-17")]
abbrev _root_.Array.toList_toArray := @List.toList_toArray

@[simp] theorem size_toArray {as : List α} : as.toArray.size = as.length := by simp [Array.size]

@[deprecated size_toArray (since := "2025-02-17")]
abbrev _root_.Array.size_toArray := @List.size_toArray

@[simp] theorem getElem_toArray {xs : List α} {i : Nat} (h : i < xs.toArray.size) :
    xs.toArray[i] = xs[i]'(by simpa using h) := rfl

@[simp] theorem getElem?_toArray {xs : List α} {i : Nat} : xs.toArray[i]? = xs[i]? := by
  simp [getElem?_def]

@[simp] theorem getElem!_toArray [Inhabited α] {xs : List α} {i : Nat} :
    xs.toArray[i]! = xs[i]! := by
  simp [getElem!_def]

end List

namespace Array

theorem size_eq_length_toList {xs : Array α} : xs.size = xs.toList.length := rfl

@[deprecated toList_toArray (since := "2024-09-09")] abbrev data_toArray := @List.toList_toArray

/-! ### Externs -/

/--
Returns the size of the array as a platform-native unsigned integer.

This is a low-level version of `Array.size` that directly queries the runtime system's
representation of arrays. While this is not provable, `Array.usize` always returns the exact size of
the array since the implementation only supports arrays of size less than `USize.size`.
-/
@[extern "lean_array_size", simp]
def usize (a : @& Array α) : USize := a.size.toUSize

/--
Low-level indexing operator which is as fast as a C array read.

This avoids overhead due to unboxing a `Nat` used as an index.
-/
@[extern "lean_array_uget", simp]
def uget (a : @& Array α) (i : USize) (h : i.toNat < a.size) : α :=
  a[i.toNat]

/--
Low-level modification operator which is as fast as a C array write. The modification is performed
in-place when the reference to the array is unique.

This avoids overhead due to unboxing a `Nat` used as an index.
-/
@[extern "lean_array_uset"]
def uset (xs : Array α) (i : USize) (v : α) (h : i.toNat < xs.size) : Array α :=
  xs.set i.toNat v h

/--
Removes the last element of an array. If the array is empty, then it is returned unmodified. The
modification is performed in-place when the reference to the array is unique.

Examples:
* `#[1, 2, 3].pop = #[1, 2]`
* `#["orange", "yellow"].pop = #["orange"]`
* `(#[] : Array String).pop = #[]`
-/
@[extern "lean_array_pop"]
def pop (xs : Array α) : Array α where
  toList := xs.toList.dropLast

@[simp] theorem size_pop {xs : Array α} : xs.pop.size = xs.size - 1 := by
  match xs with
  | ⟨[]⟩ => rfl
  | ⟨a::as⟩ => simp [pop, Nat.succ_sub_succ_eq_sub, size]

/--
Creates an array that contains `n` repetitions of `v`.

The corresponding `List` function is `List.replicate`.

Examples:
 * `Array.replicate 2 true = #[true, true]`
 * `Array.replicate 3 () = #[(), (), ()]`
 * `Array.replicate 0 "anything" = #[]`
-/
@[extern "lean_mk_array"]
def replicate {α : Type u} (n : Nat) (v : α) : Array α where
  toList := List.replicate n v

/--
Creates an array that contains `n` repetitions of `v`.

The corresponding `List` function is `List.replicate`.

Examples:
 * `Array.mkArray 2 true = #[true, true]`
 * `Array.mkArray 3 () = #[(), (), ()]`
 * `Array.mkArray 0 "anything" = #[]`
-/
@[extern "lean_mk_array", deprecated replicate (since := "2025-03-18")]
def mkArray {α : Type u} (n : Nat) (v : α) : Array α where
  toList := List.replicate n v

/--
Swaps two elements of an array. The modification is performed in-place when the reference to the
array is unique.

Examples:
* `#["red", "green", "blue", "brown"].swap 0 3 = #["brown", "green", "blue", "red"]`
* `#["red", "green", "blue", "brown"].swap 0 2 = #["blue", "green", "red", "brown"]`
* `#["red", "green", "blue", "brown"].swap 1 2 = #["red", "blue", "green", "brown"]`
* `#["red", "green", "blue", "brown"].swap 3 0 = #["brown", "green", "blue", "red"]`
-/
@[extern "lean_array_fswap"]
def swap (xs : Array α) (i j : @& Nat) (hi : i < xs.size := by get_elem_tactic) (hj : j < xs.size := by get_elem_tactic) : Array α :=
  let v₁ := xs[i]
  let v₂ := xs[j]
  let xs'  := xs.set i v₂
  xs'.set j v₁ (Nat.lt_of_lt_of_eq hj (size_set _).symm)

@[simp] theorem size_swap {xs : Array α} {i j : Nat} {hi hj} : (xs.swap i j hi hj).size = xs.size := by
  show ((xs.set i xs[j]).set j xs[i]
    (Nat.lt_of_lt_of_eq hj (size_set _).symm)).size = xs.size
  rw [size_set, size_set]

/--
Swaps two elements of an array, returning the array unchanged if either index is out of bounds. The
modification is performed in-place when the reference to the array is unique.

Examples:
* `#["red", "green", "blue", "brown"].swapIfInBounds 0 3 = #["brown", "green", "blue", "red"]`
* `#["red", "green", "blue", "brown"].swapIfInBounds 0 2 = #["blue", "green", "red", "brown"]`
* `#["red", "green", "blue", "brown"].swapIfInBounds 1 2 = #["red", "blue", "green", "brown"]`
* `#["red", "green", "blue", "brown"].swapIfInBounds 0 4 = #["red", "green", "blue", "brown"]`
* `#["red", "green", "blue", "brown"].swapIfInBounds 9 2 = #["red", "green", "blue", "brown"]`
-/
@[extern "lean_array_swap"]
def swapIfInBounds (xs : Array α) (i j : @& Nat) : Array α :=
  if h₁ : i < xs.size then
  if h₂ : j < xs.size then swap xs i j
  else xs
  else xs

@[deprecated swapIfInBounds (since := "2024-11-24")] abbrev swap! := @swapIfInBounds

/-! ### GetElem instance for `USize`, backed by `uget` -/

instance : GetElem (Array α) USize α fun xs i => i.toNat < xs.size where
  getElem xs i h := xs.uget i h

/-! ### Definitions -/

instance : EmptyCollection (Array α) := ⟨Array.empty⟩
instance : Inhabited (Array α) where
  default := Array.empty

/--
Checks whether an array is empty.

An array is empty if its size is `0`.

Examples:
 * `(#[] : Array String).isEmpty = true`
 * `#[1, 2].isEmpty = false`
 * `#[()].isEmpty = false`
-/
def isEmpty (xs : Array α) : Bool :=
  xs.size = 0

@[specialize]
def isEqvAux (xs ys : Array α) (hsz : xs.size = ys.size) (p : α → α → Bool) :
    ∀ (i : Nat) (_ : i ≤ xs.size), Bool
  | 0, _ => true
  | i+1, h =>
    p xs[i] (ys[i]'(hsz ▸ h)) && isEqvAux xs ys hsz p i (Nat.le_trans (Nat.le_add_right i 1) h)

/--
Returns `true` if `as` and `bs` have the same length and they are pairwise related by `eqv`.

Short-circuits at the first non-related pair of elements.

Examples:
* `#[1, 2, 3].isEqv #[2, 3, 4] (· < ·) = true`
* `#[1, 2, 3].isEqv #[2, 2, 4] (· < ·) = false`
* `#[1, 2, 3].isEqv #[2, 3] (· < ·) = false`
-/
@[inline] def isEqv (xs ys : Array α) (p : α → α → Bool) : Bool :=
  if h : xs.size = ys.size then
    isEqvAux xs ys h p xs.size (Nat.le_refl xs.size)
  else
    false

instance [BEq α] : BEq (Array α) :=
  ⟨fun xs ys => isEqv xs ys BEq.beq⟩

/-
`ofFn f` with `f : Fin n → α` returns the list whose ith element is `f i`.
```
ofFn f = #[f 0, f 1, ... , f(n - 1)]
``` -/
/--
Creates an array by applying `f` to each potential index in order, starting at `0`.

Examples:
 * `Array.ofFn (n := 3) toString = #["0", "1", "2"]`
 * `Array.ofFn (fun i => #["red", "green", "blue"].get i.val i.isLt) = #["red", "green", "blue"]`
-/
def ofFn {n} (f : Fin n → α) : Array α := go 0 (emptyWithCapacity n) where
  /-- Auxiliary for `ofFn`. `ofFn.go f i acc = acc ++ #[f i, ..., f(n - 1)]` -/
  @[semireducible] -- This is otherwise irreducible because it uses well-founded recursion.
  go (i : Nat) (acc : Array α) : Array α :=
    if h : i < n then go (i+1) (acc.push (f ⟨i, h⟩)) else acc
  decreasing_by simp_wf; decreasing_trivial_pre_omega

/--
Constructs an array that contains all the numbers from `0` to `n`, exclusive.

Examples:
 * `Array.range 5 := #[0, 1, 2, 3, 4]`
 * `Array.range 0 := #[]`
 * `Array.range 1 := #[0]`
-/
def range (n : Nat) : Array Nat :=
  ofFn fun (i : Fin n) => i

/--
Constructs an array of numbers of size `size`, starting at `start` and increasing by
`step` at each element.

In other words, `Array.range' start size step` is `#[start, start+step, ..., start+(len-1)*step]`.

Examples:
 * `Array.range' 0 3 (step := 1) = #[0, 1, 2]`
 * `Array.range' 0 3 (step := 2) = #[0, 2, 4]`
 * `Array.range' 0 4 (step := 2) = #[0, 2, 4, 6]`
 * `Array.range' 3 4 (step := 2) = #[3, 5, 7, 9]`
-/
def range' (start size : Nat) (step : Nat := 1) : Array Nat :=
  ofFn fun (i : Fin size) => start + step * i

/--
Constructs a single-element array that contains `v`.

Examples:
 * `Array.singleton 5 = #[5]`
 * `Array.singleton "one" = #["one"]`
-/
@[inline] protected def singleton (v : α) : Array α := #[v]

/--
Returns the last element of an array, or panics if the array is empty.

Safer alternatives include `Array.back`, which requires a proof the array is non-empty, and
`Array.back?`, which returns an `Option`.
-/
def back! [Inhabited α] (xs : Array α) : α :=
  xs[xs.size - 1]!

/--
Returns the last element of an array, given a proof that the array is not empty.

See `Array.back!` for the version that panics if the array is empty, or `Array.back?` for the
version that returns an option.
-/
def back (xs : Array α) (h : 0 < xs.size := by get_elem_tactic) : α :=
  xs[xs.size - 1]'(Nat.sub_one_lt_of_lt h)

/--
Returns the last element of an array, or `none` if the array is empty.

See `Array.back!` for the version that panics if the array is empty, or `Array.back` for the version
that requires a proof the array is non-empty.
-/
def back? (xs : Array α) : Option α :=
  xs[xs.size - 1]?

@[deprecated "Use `a[i]?` instead." (since := "2025-02-12")]
def get? (xs : Array α) (i : Nat) : Option α :=
  if h : i < xs.size then some xs[i] else none

/--
Swaps a new element with the element at the given index.

Returns the value formerly found at `i`, paired with an array in which the value at `i` has been
replaced with `v`.

Examples:
* `#["spinach", "broccoli", "carrot"].swapAt 1 "pepper" = ("broccoli", #["spinach", "pepper", "carrot"])`
* `#["spinach", "broccoli", "carrot"].swapAt 2 "pepper" = ("carrot", #["spinach", "broccoli", "pepper"])`
-/
@[inline] def swapAt (xs : Array α) (i : Nat) (v : α) (hi : i < xs.size := by get_elem_tactic) : α × Array α :=
  let e := xs[i]
  let xs' := xs.set i v
  (e, xs')

/--
Swaps a new element with the element at the given index. Panics if the index is out of bounds.

Returns the value formerly found at `i`, paired with an array in which the value at `i` has been
replaced with `v`.

Examples:
* `#["spinach", "broccoli", "carrot"].swapAt! 1 "pepper" = (#["spinach", "pepper", "carrot"], "broccoli")`
* `#["spinach", "broccoli", "carrot"].swapAt! 2 "pepper" = (#["spinach", "broccoli", "pepper"], "carrot")`
-/
@[inline]
def swapAt! (xs : Array α) (i : Nat) (v : α) : α × Array α :=
  if h : i < xs.size then
    swapAt xs i v
  else
    have : Inhabited (α × Array α) := ⟨(v, xs)⟩
    panic! ("index " ++ toString i ++ " out of bounds")

/--
Returns the first `n` elements of an array. The resulting array is produced by repeatedly calling
`Array.pop`. If `n` is greater than the size of the array, it is returned unmodified.

If the reference to the array is unique, then this function uses in-place modification.

Examples:
* `#[0, 1, 2, 3, 4].shrink 2 = #[0, 1]`
* `#[0, 1, 2, 3, 4].shrink 0 = #[]`
* `#[0, 1, 2, 3, 4].shrink 10 = #[0, 1, 2, 3, 4]`
-/
def shrink (xs : Array α) (n : Nat) : Array α :=
  let rec loop
    | 0,   xs => xs
    | n+1, xs => loop n xs.pop
  loop (xs.size - n) xs

/--
Returns a new array that contains the first `i` elements of `xs`. If `xs` has fewer than `i`
elements, the new array contains all the elements of `xs`.

The returned array is always a new array, even if it contains the same elements as the input array.

Examples:
* `#["red", "green", "blue"].take 1 = #["red"]`
* `#["red", "green", "blue"].take 2 = #["red", "green"]`
* `#["red", "green", "blue"].take 5 = #["red", "green", "blue"]`
-/
abbrev take (xs : Array α) (i : Nat) : Array α := extract xs 0 i

@[simp] theorem take_eq_extract {xs : Array α} {i : Nat} : xs.take i = xs.extract 0 i := rfl

/--
Removes the first `i` elements of `xs`. If `xs` has fewer than `i` elements, the new array is empty.

The returned array is always a new array, even if it contains the same elements as the input array.

Examples:
* `#["red", "green", "blue"].drop 1 = #["green", "blue"]`
* `#["red", "green", "blue"].drop 2 = #["blue"]`
* `#["red", "green", "blue"].drop 5 = #[]`
-/
abbrev drop (xs : Array α) (i : Nat) : Array α := extract xs i xs.size

@[simp] theorem drop_eq_extract {xs : Array α} {i : Nat} : xs.drop i = xs.extract i xs.size := rfl

@[inline]
unsafe def modifyMUnsafe [Monad m] (xs : Array α) (i : Nat) (f : α → m α) : m (Array α) := do
  if h : i < xs.size then
    let v                := xs[i]
    -- Replace a[i] by `box(0)`.  This ensures that `v` remains unshared if possible.
    -- Note: we assume that arrays have a uniform representation irrespective
    -- of the element type, and that it is valid to store `box(0)` in any array.
    let xs'               := xs.set i (unsafeCast ())
    let v ← f v
    pure <| xs'.set i v (Nat.lt_of_lt_of_eq h (size_set ..).symm)
  else
    pure xs

/--
Replaces the element at the given index, if it exists, with the result of applying the monadic
function `f` to it. If the index is invalid, the array is returned unmodified and `f` is not called.

Examples:
```lean example
#eval #[1, 2, 3, 4].modifyM 2 fun x => do
  IO.println s!"It was {x}"
  return x * 10
```
```output
It was 3
```
```output
#[1, 2, 30, 4]
```

```lean example
#eval #[1, 2, 3, 4].modifyM 6 fun x => do
  IO.println s!"It was {x}"
  return x * 10
```
```output
#[1, 2, 3, 4]
```
-/
@[implemented_by modifyMUnsafe]
def modifyM [Monad m] (xs : Array α) (i : Nat) (f : α → m α) : m (Array α) := do
  if h : i < xs.size then
    let v   := xs[i]
    let v ← f v
    pure <| xs.set i v
  else
    pure xs

/--
Replaces the element at the given index, if it exists, with the result of applying `f` to it. If the
index is invalid, the array is returned unmodified.

Examples:
 * `#[1, 2, 3].modify 0 (· * 10) = #[10, 2, 3]`
 * `#[1, 2, 3].modify 2 (· * 10) = #[1, 2, 30]`
 * `#[1, 2, 3].modify 3 (· * 10) = #[1, 2, 3]`
-/
@[inline]
def modify (xs : Array α) (i : Nat) (f : α → α) : Array α :=
  Id.run <| modifyM xs i f

set_option linter.indexVariables false in -- Changing `idx` causes bootstrapping issues, haven't investigated.
/--
Replaces the element at the given index, if it exists, with the result of applying `f` to it. If the
index is invalid, the array is returned unmodified.

Examples:
 * `#[1, 2, 3].modifyOp 0 (· * 10) = #[10, 2, 3]`
 * `#[1, 2, 3].modifyOp 2 (· * 10) = #[1, 2, 30]`
 * `#[1, 2, 3].modifyOp 3 (· * 10) = #[1, 2, 3]`
-/
@[inline]
def modifyOp (xs : Array α) (idx : Nat) (f : α → α) : Array α :=
  xs.modify idx f

/--
  We claim this unsafe implementation is correct because an array cannot have more than `usizeSz` elements in our runtime.

  This kind of low level trick can be removed with a little bit of compiler support. For example, if the compiler simplifies `as.size < usizeSz` to true. -/
@[inline] unsafe def forIn'Unsafe {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (as : Array α) (b : β) (f : (a : α) → a ∈ as → β → m (ForInStep β)) : m β :=
  let sz := as.usize
  let rec @[specialize] loop (i : USize) (b : β) : m β := do
    if i < sz then
      let a := as.uget i lcProof
      match (← f a lcProof b) with
      | ForInStep.done  b => pure b
      | ForInStep.yield b => loop (i+1) b
    else
      pure b
  loop 0 b

/-- Reference implementation for `forIn'` -/
@[implemented_by Array.forIn'Unsafe]
protected def forIn' {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (as : Array α) (b : β) (f : (a : α) → a ∈ as → β → m (ForInStep β)) : m β :=
  let rec loop (i : Nat) (h : i ≤ as.size) (b : β) : m β := do
    match i, h with
    | 0,   _ => pure b
    | i+1, h =>
      have h' : i < as.size            := Nat.lt_of_lt_of_le (Nat.lt_succ_self i) h
      have : as.size - 1 < as.size     := Nat.sub_lt (Nat.zero_lt_of_lt h') (by decide)
      have : as.size - 1 - i < as.size := Nat.lt_of_le_of_lt (Nat.sub_le (as.size - 1) i) this
      match (← f as[as.size - 1 - i] (getElem_mem this) b) with
      | ForInStep.done b  => pure b
      | ForInStep.yield b => loop i (Nat.le_of_lt h') b
  loop as.size (Nat.le_refl _) b

instance : ForIn' m (Array α) α inferInstance where
  forIn' := Array.forIn'

-- No separate `ForIn` instance is required because it can be derived from `ForIn'`.

-- We simplify `Array.forIn'` to `forIn'`.
@[simp] theorem forIn'_eq_forIn' [Monad m] : @Array.forIn' α β m _ = forIn' := rfl

/-- See comment at `forIn'Unsafe` -/
@[inline]
unsafe def foldlMUnsafe {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (f : β → α → m β) (init : β) (as : Array α) (start := 0) (stop := as.size) : m β :=
  let rec @[specialize] fold (i : USize) (stop : USize) (b : β) : m β := do
    if i == stop then
      pure b
    else
      fold (i+1) stop (← f b (as.uget i lcProof))
  if start < stop then
    if stop ≤ as.size then
      fold (USize.ofNat start) (USize.ofNat stop) init
    else
      pure init
  else
    pure init

/--
Folds a monadic function over a list from the left, accumulating a value starting with `init`. The
accumulated value is combined with the each element of the list in order, using `f`.

The optional parameters `start` and `stop` control the region of the array to be folded. Folding
proceeds from `start` (inclusive) to `stop` (exclusive), so no folding occurs unless `start < stop`.
By default, the entire array is folded.

Examples:
```lean example
example [Monad m] (f : α → β → m α) :
    Array.foldlM (m := m) f x₀ #[a, b, c] = (do
      let x₁ ← f x₀ a
      let x₂ ← f x₁ b
      let x₃ ← f x₂ c
      pure x₃)
  := by rfl
```

```lean example
example [Monad m] (f : α → β → m α) :
    Array.foldlM (m := m) f x₀ #[a, b, c] (start := 1) = (do
      let x₁ ← f x₀ b
      let x₂ ← f x₁ c
      pure x₂)
  := by rfl
```
-/
-- Reference implementation for `foldlM`
@[implemented_by foldlMUnsafe]
def foldlM {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (f : β → α → m β) (init : β) (as : Array α) (start := 0) (stop := as.size) : m β :=
  let fold (stop : Nat) (h : stop ≤ as.size) :=
    let rec loop (i : Nat) (j : Nat) (b : β) : m β := do
      if hlt : j < stop then
        match i with
        | 0    => pure b
        | i'+1 =>
          have : j < as.size := Nat.lt_of_lt_of_le hlt h
          loop i' (j+1) (← f b as[j])
      else
        pure b
    loop (stop - start) start init
  if h : stop ≤ as.size then
    fold stop h
  else
    fold as.size (Nat.le_refl _)

/-- See comment at `forIn'Unsafe` -/
@[inline]
unsafe def foldrMUnsafe {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (f : α → β → m β) (init : β) (as : Array α) (start := as.size) (stop := 0) : m β :=
  let rec @[specialize] fold (i : USize) (stop : USize) (b : β) : m β := do
    if i == stop then
      pure b
    else
      fold (i-1) stop (← f (as.uget (i-1) lcProof) b)
  if start ≤ as.size then
    if stop < start then
      fold (USize.ofNat start) (USize.ofNat stop) init
    else
      pure init
  else if stop < as.size then
    fold (USize.ofNat as.size) (USize.ofNat stop) init
  else
    pure init

/--
Folds a monadic function over an array from the right, accumulating a value starting with `init`.
The accumulated value is combined with the each element of the list in reverse order, using `f`.

The optional parameters `start` and `stop` control the region of the array to be folded. Folding
proceeds from `start` (exclusive) to `stop` (inclusive), so no folding occurs unless `start > stop`.
By default, the entire array is folded.

Examples:
```lean example
example [Monad m] (f : α → β → m β) :
  Array.foldrM (m := m) f x₀ #[a, b, c] = (do
    let x₁ ← f c x₀
    let x₂ ← f b x₁
    let x₃ ← f a x₂
    pure x₃)
  := by rfl
```

```lean example
example [Monad m] (f : α → β → m β) :
  Array.foldrM (m := m) f x₀ #[a, b, c] (start := 2) = (do
    let x₁ ← f b x₀
    let x₂ ← f a x₁
    pure x₂)
  := by rfl
```
-/
-- Reference implementation for `foldrM`
@[implemented_by foldrMUnsafe]
def foldrM {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (f : α → β → m β) (init : β) (as : Array α) (start := as.size) (stop := 0) : m β :=
  let rec fold (i : Nat) (h : i ≤ as.size) (b : β) : m β := do
    if i == stop then
      pure b
    else match i, h with
      | 0, _   => pure b
      | i+1, h =>
        have : i < as.size := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) h
        fold i (Nat.le_of_lt this) (← f as[i] b)
  if h : start ≤ as.size then
    if stop < start then
      fold start h init
    else
      pure init
  else if stop < as.size then
    fold as.size (Nat.le_refl _) init
  else
    pure init

/-- See comment at `forIn'Unsafe` -/
@[inline]
unsafe def mapMUnsafe {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (f : α → m β) (as : Array α) : m (Array β) :=
  let sz := as.usize
  let rec @[specialize] map (i : USize) (bs : Array NonScalar) : m (Array PNonScalar.{v}) := do
    if i < sz then
     let v    := bs.uget i lcProof
     -- Replace bs[i] by `box(0)`.  This ensures that `v` remains unshared if possible.
     -- Note: we assume that arrays have a uniform representation irrespective
     -- of the element type, and that it is valid to store `box(0)` in any array.
     let bs'    := bs.uset i default lcProof
     let vNew ← f (unsafeCast v)
     map (i+1) (bs'.uset i (unsafeCast vNew) lcProof)
    else
     pure (unsafeCast bs)
  unsafeCast <| map 0 (unsafeCast as)

/--
Applies the monadic action `f` to every element in the array, left-to-right, and returns the array
of results.
-/
-- Reference implementation for `mapM`
@[implemented_by mapMUnsafe]
def mapM {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (f : α → m β) (as : Array α) : m (Array β) :=
  -- Note: we cannot use `foldlM` here for the reference implementation because this calls
  -- `bind` and `pure` too many times. (We are not assuming `m` is a `LawfulMonad`)
  let rec @[semireducible] -- This is otherwise irreducible because it uses well-founded recursion.
    map (i : Nat) (bs : Array β) : m (Array β) := do
      if hlt : i < as.size then
        map (i+1) (bs.push (← f as[i]))
      else
        pure bs
  decreasing_by simp_wf; decreasing_trivial_pre_omega
  map 0 (emptyWithCapacity as.size)

@[deprecated mapM (since := "2024-11-11")] abbrev sequenceMap := @mapM

/--
Applies the monadic action `f` to every element in the array, along with the element's index and a
proof that the index is in bounds, from left to right. Returns the array of results.
-/
@[inline]
def mapFinIdxM {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m]
    (as : Array α) (f : (i : Nat) → α → (h : i < as.size) → m β) : m (Array β) :=
  let rec @[specialize] map (i : Nat) (j : Nat) (inv : i + j = as.size) (bs : Array β) : m (Array β) := do
    match i, inv with
    | 0,    _  => pure bs
    | i+1, inv =>
      have j_lt : j < as.size := by
        rw [← inv, Nat.add_assoc, Nat.add_comm 1 j, Nat.add_comm]
        apply Nat.le_add_right
      have : i + (j + 1) = as.size := by rw [← inv, Nat.add_comm j 1, Nat.add_assoc]
      map i (j+1) this (bs.push (← f j as[j] j_lt))
  map as.size 0 rfl (emptyWithCapacity as.size)

/--
Applies the monadic action `f` to every element in the array, along with the element's index, from
left to right. Returns the array of results.
-/
@[inline]
def mapIdxM {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (f : Nat → α → m β) (as : Array α) : m (Array β) :=
  as.mapFinIdxM fun i a _ => f i a

/--
Maps `f` over the array and collects the results with `<|>`. The result for the end of the array is
`failure`.

Examples:
 * `#[[], [1, 2], [], [2]].firstM List.head? = some 1`
 * `#[[], [], []].firstM List.head? = none`
 * `#[].firstM List.head? = none`
-/
@[inline]
def firstM {α : Type u} {m : Type v → Type w} [Alternative m] (f : α → m β) (as : Array α) : m β :=
  go 0
where
  go (i : Nat) : m β :=
    if hlt : i < as.size then
      f as[i] <|> go (i+1)
    else
      failure
  termination_by as.size - i
  decreasing_by exact Nat.sub_succ_lt_self as.size i hlt

/--
Returns the first non-`none` result of applying the monadic function `f` to each element of the
array, in order. Returns `none` if `f` returns `none` for all elements.

Example:
```lean example
#eval #[7, 6, 5, 8, 1, 2, 6].findSomeM? fun i => do
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
def findSomeM? {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (f : α → m (Option β)) (as : Array α) : m (Option β) := do
  for a in as do
    match (← f a) with
    | some b => return b
    | _      => pure ⟨⟩
  return none

/--
Returns the first element of the array for which the monadic predicate `p` returns `true`, or `none`
if no such element is found. Elements of the array are checked in order.

The monad `m` is restricted to `Type → Type` to avoid needing to use `ULift Bool` in `p`'s type.

Example:
```lean example
#eval #[7, 6, 5, 8, 1, 2, 6].findM? fun i => do
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
def findM? {α : Type} [Monad m] (p : α → m Bool) (as : Array α) : m (Option α) := do
  for a in as do
    if (← p a) then
      return a
  return none

/--
Finds the index of the first element of an array for which the monadic predicate `p` returns `true`.
Elements are examined in order from left to right, and the search is terminated when an element that
satisfies `p` is found. If no such element exists in the array, then `none` is returned.
-/
@[inline]
def findIdxM? [Monad m] (p : α → m Bool) (as : Array α) : m (Option Nat) := do
  let mut i := 0
  for a in as do
    if (← p a) then
      return some i
    i := i + 1
  return none

@[inline]
unsafe def anyMUnsafe {α : Type u} {m : Type → Type w} [Monad m] (p : α → m Bool) (as : Array α) (start := 0) (stop := as.size) : m Bool :=
  let rec @[specialize] any (i : USize) (stop : USize) : m Bool := do
    if i == stop then
      pure false
    else
      if (← p (as.uget i lcProof)) then
        pure true
      else
        any (i+1) stop
  if start < stop then
    let stop' := min stop as.size
    if start < stop' then
      any (USize.ofNat start) (USize.ofNat stop')
    else
      pure false
  else
    pure false

/--
Returns `true` if the monadic predicate `p` returns `true` for any element of `as`.

Short-circuits upon encountering the first `true`. The elements in `as` are examined in order from
left to right.

The optional parameters `start` and `stop` control the region of the array to be checked. Only the
elements with indices from `start` (inclusive) to `stop` (exclusive) are checked. By default, the
entire array is checked.
-/
@[implemented_by anyMUnsafe]
def anyM {α : Type u} {m : Type → Type w} [Monad m] (p : α → m Bool) (as : Array α) (start := 0) (stop := as.size) : m Bool :=
  let any (stop : Nat) (h : stop ≤ as.size) :=
    let rec @[semireducible] -- This is otherwise irreducible because it uses well-founded recursion.
    loop (j : Nat) : m Bool := do
      if hlt : j < stop then
        have : j < as.size := Nat.lt_of_lt_of_le hlt h
        if (← p as[j]) then
          pure true
        else
          loop (j+1)
      else
        pure false
      decreasing_by simp_wf; decreasing_trivial_pre_omega
    loop start
  if h : stop ≤ as.size then
    any stop h
  else
    any as.size (Nat.le_refl _)

/--
Returns `true` if the monadic predicate `p` returns `true` for every element of `as`.

Short-circuits upon encountering the first `false`. The elements in `as` are examined in order from
left to right.

The optional parameters `start` and `stop` control the region of the array to be checked. Only the
elements with indices from `start` (inclusive) to `stop` (exclusive) are checked. By default, the
entire array is checked.
-/
@[inline]
def allM {α : Type u} {m : Type → Type w} [Monad m] (p : α → m Bool) (as : Array α) (start := 0) (stop := as.size) : m Bool :=
  return !(← as.anyM (start := start) (stop := stop) fun v => return !(← p v))

/--
Returns the first non-`none` result of applying the monadic function `f` to each element of the
array in reverse order, from right to left. Once a non-`none` result is found, no further elements
are checked. Returns `none` if `f` returns `none` for all elements of the array.

Examples:
```lean example
#eval #[1, 2, 0, -4, 1].findSomeRevM? (m := Except String) fun x => do
  if x = 0 then throw "Zero!"
  else if x < 0 then return (some x)
  else return none
```
```output
Except.ok (some (-4))
```
```lean example
#eval #[1, 2, 0, 4, 1].findSomeRevM? (m := Except String) fun x => do
  if x = 0 then throw "Zero!"
  else if x < 0 then return (some x)
  else return none
```
```output
Except.error "Zero!"
```
-/
@[inline]
def findSomeRevM? {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (f : α → m (Option β)) (as : Array α) : m (Option β) :=
  let rec @[specialize] find : (i : Nat) → i ≤ as.size → m (Option β)
    | 0,   _ => pure none
    | i+1, h => do
      have : i < as.size := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) h
      let r ← f as[i]
      match r with
      | some _ => pure r
      | none   =>
        have : i ≤ as.size := Nat.le_of_lt this
        find i this
  find as.size (Nat.le_refl _)

/--
Returns the last element of the array for which the monadic predicate `p` returns `true`, or `none`
if no such element is found. Elements of the array are checked in reverse, from right to left..

The monad `m` is restricted to `Type → Type` to avoid needing to use `ULift Bool` in `p`'s type.

Example:
```lean example
#eval #[7, 5, 8, 1, 2, 6, 5, 8].findRevM? fun i => do
  if i < 5 then
    return true
  if i ≤ 6 then
    IO.println s!"Almost! {i}"
  return false
```
```output
Almost! 5
Almost! 6
```
```output
some 2
```
-/
@[inline]
def findRevM? {α : Type} {m : Type → Type w} [Monad m] (p : α → m Bool) (as : Array α) : m (Option α) :=
  as.findSomeRevM? fun a => return if (← p a) then some a else none

/--
Applies the monadic action `f` to each element of an array, in order.

The optional parameters `start` and `stop` control the region of the array to which `f` should be
applied. Iteration proceeds from `start` (inclusive) to `stop` (exclusive), so `f` is not invoked
unless `start < stop`. By default, the entire array is used.
-/
@[inline]
protected def forM {α : Type u} {m : Type v → Type w} [Monad m] (f : α → m PUnit) (as : Array α) (start := 0) (stop := as.size) : m PUnit :=
  as.foldlM (fun _ => f) ⟨⟩ start stop

instance : ForM m (Array α) α where
  forM xs f := Array.forM f xs

-- We simplify `Array.forM` to `forM`.
@[simp] theorem forM_eq_forM [Monad m] {f : α → m PUnit} :
    Array.forM f as 0 as.size = forM as f := rfl

/--
Applies the monadic action `f` to each element of an array from right to left, in reverse order.

The optional parameters `start` and `stop` control the region of the array to which `f` should be
applied. Iteration proceeds from `start` (exclusive) to `stop` (inclusive), so no `f` is not invoked
unless `start > stop`. By default, the entire array is used.
-/
@[inline]
def forRevM {α : Type u} {m : Type v → Type w} [Monad m] (f : α → m PUnit) (as : Array α) (start := as.size) (stop := 0) : m PUnit :=
  as.foldrM (fun a _ => f a) ⟨⟩ start stop

/--
Folds a function over an array from the left, accumulating a value starting with `init`. The
accumulated value is combined with the each element of the array in order, using `f`.

The optional parameters `start` and `stop` control the region of the array to be folded. Folding
proceeds from `start` (inclusive) to `stop` (exclusive), so no folding occurs unless `start < stop`.
By default, the entire array is used.

Examples:
 * `#[a, b, c].foldl f z  = f (f (f z a) b) c`
 * `#[1, 2, 3].foldl (· ++ toString ·) "" = "123"`
 * `#[1, 2, 3].foldl (s!"({·} {·})") "" = "((( 1) 2) 3)"`
-/
@[inline]
def foldl {α : Type u} {β : Type v} (f : β → α → β) (init : β) (as : Array α) (start := 0) (stop := as.size) : β :=
  Id.run <| as.foldlM f init start stop

/--
Folds a function over an array from the right, accumulating a value starting with `init`. The
accumulated value is combined with the each element of the array in reverse order, using `f`.

The optional parameters `start` and `stop` control the region of the array to be folded. Folding
proceeds from `start` (exclusive) to `stop` (inclusive), so no folding occurs unless `start > stop`.
By default, the entire array is used.

Examples:
 * `#[a, b, c].foldr f init  = f a (f b (f c init))`
 * `#[1, 2, 3].foldr (toString · ++ ·) "" = "123"`
 * `#[1, 2, 3].foldr (s!"({·} {·})") "!" = "(1 (2 (3 !)))"`
-/
@[inline]
def foldr {α : Type u} {β : Type v} (f : α → β → β) (init : β) (as : Array α) (start := as.size) (stop := 0) : β :=
  Id.run <| as.foldrM f init start stop

/--
Computes the sum of the elements of an array.

Examples:
 * `#[a, b, c].sum = a + (b + (c + 0))`
 * `#[1, 2, 5].sum = 8`
-/
@[inline]
def sum {α} [Add α] [Zero α] : Array α → α :=
  foldr (· + ·) 0

/--
Counts the number of elements in the array `as` that satisfy the Boolean predicate `p`.

Examples:
 * `#[1, 2, 3, 4, 5].countP (· % 2 == 0) = 2`
 * `#[1, 2, 3, 4, 5].countP (· < 5) = 4`
 * `#[1, 2, 3, 4, 5].countP (· > 5) = 0`
-/
@[inline]
def countP {α : Type u} (p : α → Bool) (as : Array α) : Nat :=
  as.foldr (init := 0) fun a acc => bif p a then acc + 1 else acc

/--
Counts the number of times an element occurs in an array.

Examples:
 * `#[1, 1, 2, 3, 5].count 1 = 2`
 * `#[1, 1, 2, 3, 5].count 5 = 1`
 * `#[1, 1, 2, 3, 5].count 4 = 0`
-/
@[inline]
def count {α : Type u} [BEq α] (a : α) (as : Array α) : Nat :=
  countP (· == a) as

/--
Applies a function to each element of the array, returning the resulting array of values.

Examples:
* `#[a, b, c].map f = #[f a, f b, f c]`
* `#[].map Nat.succ = #[]`
* `#["one", "two", "three"].map (·.length) = #[3, 3, 5]`
* `#["one", "two", "three"].map (·.reverse) = #["eno", "owt", "eerht"]`
-/
@[inline]
def map {α : Type u} {β : Type v} (f : α → β) (as : Array α) : Array β :=
  Id.run <| as.mapM f

instance : Functor Array where
  map := map

/--
Applies a function to each element of the array along with the index at which that element is found,
returning the array of results. In addition to the index, the function is also provided with a proof
that the index is valid.

`Array.mapIdx` is a variant that does not provide the function with evidence that the index is
valid.
-/
@[inline]
def mapFinIdx {α : Type u} {β : Type v} (as : Array α) (f : (i : Nat) → α → (h : i < as.size) → β) : Array β :=
  Id.run <| as.mapFinIdxM f

/--
Applies a function to each element of the array along with the index at which that element is found,
returning the array of results.

`Array.mapFinIdx` is a variant that additionally provides the function with a proof that the index
is valid.
-/
@[inline]
def mapIdx {α : Type u} {β : Type v} (f : Nat → α → β) (as : Array α) : Array β :=
  Id.run <| as.mapIdxM f

/--
Pairs each element of an array with its index, optionally starting from an index other than `0`.

Examples:
* `#[a, b, c].zipIdx = #[(a, 0), (b, 1), (c, 2)]`
* `#[a, b, c].zipIdx 5 = #[(a, 5), (b, 6), (c, 7)]`
-/
def zipIdx (xs : Array α) (start := 0) : Array (α × Nat) :=
  xs.mapIdx fun i a => (a, start + i)

@[deprecated zipIdx (since := "2025-01-21")] abbrev zipWithIndex := @zipIdx

/--
Returns the first element of the array for which the predicate `p` returns `true`, or `none` if no
such element is found.

Examples:
* `#[7, 6, 5, 8, 1, 2, 6].find? (· < 5) = some 1`
* `#[7, 6, 5, 8, 1, 2, 6].find? (· < 1) = none`
-/
@[inline]
def find? {α : Type u} (p : α → Bool) (as : Array α) : Option α :=
  Id.run do
    for a in as do
      if p a then
        return a
    return none

/--
Returns the first non-`none` result of applying the function `f` to each element of the
array, in order. Returns `none` if `f` returns `none` for all elements.

Example:
```lean example
#eval #[7, 6, 5, 8, 1, 2, 6].findSome? fun i =>
  if i < 5 then
    some (i * 10)
  else
    none
```
```output
some 10
```
-/
@[inline]
def findSome? {α : Type u} {β : Type v} (f : α → Option β) (as : Array α) : Option β :=
  Id.run <| as.findSomeM? f

/--
Returns the first non-`none` result of applying the function `f` to each element of the
array, in order. Panics if `f` returns `none` for all elements.

Example:
```lean example
#eval #[7, 6, 5, 8, 1, 2, 6].findSome? fun i =>
  if i < 5 then
    some (i * 10)
  else
    none
```
```output
some 10
```
-/
@[inline]
def findSome! {α : Type u} {β : Type v} [Inhabited β] (f : α → Option β) (xs : Array α) : β :=
  match xs.findSome? f with
  | some b => b
  | none   => panic! "failed to find element"

/--
Returns the first non-`none` result of applying `f` to each element of the array in reverse order,
from right to left. Returns `none` if `f` returns `none` for all elements of the array.

Examples:
 * `#[7, 6, 5, 8, 1, 2, 6].findSome? (fun x => if x < 5 then some (10 * x) else none) = some 10`
 * `#[7, 6, 5, 8, 1, 2, 6].findSome? (fun x => if x < 1 then some (10 * x) else none) = none`
-/
@[inline]
def findSomeRev? {α : Type u} {β : Type v} (f : α → Option β) (as : Array α) : Option β :=
  Id.run <| as.findSomeRevM? f

/--
Returns the last element of the array for which the predicate `p` returns `true`, or `none` if no
such element is found.

Examples:
* `#[7, 6, 5, 8, 1, 2, 6].findRev? (· < 5) = some 2`
* `#[7, 6, 5, 8, 1, 2, 6].findRev? (· < 1) = none`
-/
@[inline]
def findRev? {α : Type} (p : α → Bool) (as : Array α) : Option α :=
  Id.run <| as.findRevM? p

/--
Returns the index of the first element for which `p` returns `true`, or `none` if there is no such
element.

Examples:
* `#[7, 6, 5, 8, 1, 2, 6].findIdx (· < 5) = some 4`
* `#[7, 6, 5, 8, 1, 2, 6].findIdx (· < 1) = none`
-/
@[inline]
def findIdx? {α : Type u} (p : α → Bool) (as : Array α) : Option Nat :=
  let rec @[semireducible] -- This is otherwise irreducible because it uses well-founded recursion.
  loop (j : Nat) :=
    if h : j < as.size then
      if p as[j] then some j else loop (j + 1)
    else none
    decreasing_by simp_wf; decreasing_trivial_pre_omega
  loop 0

/--
Returns the index of the first element for which `p` returns `true`, or `none` if there is no such
element. The index is returned as a `Fin`, which guarantees that it is in bounds.

Examples:
* `#[7, 6, 5, 8, 1, 2, 6].findFinIdx? (· < 5) = some (4 : Fin 7)`
* `#[7, 6, 5, 8, 1, 2, 6].findFinIdx? (· < 1) = none`
-/
@[inline]
def findFinIdx? {α : Type u} (p : α → Bool) (as : Array α) : Option (Fin as.size) :=
  let rec @[semireducible] -- This is otherwise irreducible because it uses well-founded recursion.
  loop (j : Nat) :=
    if h : j < as.size then
      if p as[j] then some ⟨j, h⟩ else loop (j + 1)
    else none
    decreasing_by simp_wf; decreasing_trivial_pre_omega
  loop 0

theorem findIdx?_loop_eq_map_findFinIdx?_loop_val {xs : Array α} {p : α → Bool} {j} :
    findIdx?.loop p xs j = (findFinIdx?.loop p xs j).map (·.val) := by
  unfold findIdx?.loop
  unfold findFinIdx?.loop
  split <;> rename_i h
  case isTrue =>
    split
    case isTrue => simp
    case isFalse =>
      have : xs.size - (j + 1) < xs.size - j := Nat.sub_succ_lt_self xs.size j h
      rw [findIdx?_loop_eq_map_findFinIdx?_loop_val (j := j + 1)]
  case isFalse => simp
termination_by xs.size - j

theorem findIdx?_eq_map_findFinIdx?_val {xs : Array α} {p : α → Bool} :
    xs.findIdx? p = (xs.findFinIdx? p).map (·.val) := by
  simp [findIdx?, findFinIdx?, findIdx?_loop_eq_map_findFinIdx?_loop_val]

/--
Returns the index of the first element for which `p` returns `true`, or the size of the array if
there is no such element.

Examples:
* `#[7, 6, 5, 8, 1, 2, 6].findIdx (· < 5) = 4`
* `#[7, 6, 5, 8, 1, 2, 6].findIdx (· < 1) = 7`
-/
@[inline]
def findIdx (p : α → Bool) (as : Array α) : Nat := (as.findIdx? p).getD as.size

@[semireducible] -- This is otherwise irreducible because it uses well-founded recursion.
def idxOfAux [BEq α] (xs : Array α) (v : α) (i : Nat) : Option (Fin xs.size) :=
  if h : i < xs.size then
    if xs[i] == v then some ⟨i, h⟩
    else idxOfAux xs v (i+1)
  else none
decreasing_by simp_wf; decreasing_trivial_pre_omega

@[deprecated idxOfAux (since := "2025-01-29")]
abbrev indexOfAux := @idxOfAux

/--
Returns the index of the first element equal to `a`, or the size of the array if no element is equal
to `a`. The index is returned as a `Fin`, which guarantees that it is in bounds.

Examples:
 * `#["carrot", "potato", "broccoli"].finIdxOf? "carrot" = some 0`
 * `#["carrot", "potato", "broccoli"].finIdxOf? "broccoli" = some 2`
 * `#["carrot", "potato", "broccoli"].finIdxOf? "tomato" = none`
 * `#["carrot", "potato", "broccoli"].finIdxOf? "anything else" = none`
-/
def finIdxOf? [BEq α] (xs : Array α) (v : α) : Option (Fin xs.size) :=
  idxOfAux xs v 0

@[deprecated "`Array.indexOf?` has been deprecated, use `idxOf?` or `finIdxOf?` instead." (since := "2025-01-29")]
abbrev indexOf? := @finIdxOf?

/--
Returns the index of the first element equal to `a`, or the size of the array if no element is equal
to `a`.

Examples:
 * `#["carrot", "potato", "broccoli"].idxOf "carrot" = 0`
 * `#["carrot", "potato", "broccoli"].idxOf "broccoli" = 2`
 * `#["carrot", "potato", "broccoli"].idxOf "tomato" = 3`
 * `#["carrot", "potato", "broccoli"].idxOf "anything else" = 3`
-/
def idxOf [BEq α] (a : α) : Array α → Nat := findIdx (· == a)

/--
Returns the index of the first element equal to `a`, or `none` if no element is equal to `a`.

Examples:
 * `#["carrot", "potato", "broccoli"].idxOf? "carrot" = some 0`
 * `#["carrot", "potato", "broccoli"].idxOf? "broccoli" = some 2`
 * `#["carrot", "potato", "broccoli"].idxOf? "tomato" = none`
 * `#["carrot", "potato", "broccoli"].idxOf? "anything else" = none`
-/
def idxOf? [BEq α] (xs : Array α) (v : α) : Option Nat :=
  (xs.finIdxOf? v).map (·.val)

@[deprecated idxOf? (since := "2024-11-20")]
def getIdx? [BEq α] (xs : Array α) (v : α) : Option Nat :=
  xs.findIdx? fun a => a == v

/--
Returns `true` if `p` returns `true` for any element of `as`.

Short-circuits upon encountering the first `true`.

The optional parameters `start` and `stop` control the region of the array to be checked. Only the
elements with indices from `start` (inclusive) to `stop` (exclusive) are checked. By default, the
entire array is checked.

Examples:
* `#[2, 4, 6].any (· % 2 = 0) = true`
* `#[2, 4, 6].any (· % 2 = 1) = false`
* `#[2, 4, 5, 6].any (· % 2 = 0) = true`
* `#[2, 4, 5, 6].any (· % 2 = 1) = true`
-/
@[inline]
def any (as : Array α) (p : α → Bool) (start := 0) (stop := as.size) : Bool :=
  Id.run <| as.anyM p start stop

/--
Returns `true` if `p` returns `true` for every element of `as`.

Short-circuits upon encountering the first `false`.

The optional parameters `start` and `stop` control the region of the array to be checked. Only the
elements with indices from `start` (inclusive) to `stop` (exclusive) are checked. By default, the
entire array is checked.

Examples:
* `#[a, b, c].all p = (p a && (p b && p c))`
* `#[2, 4, 6].all (· % 2 = 0) = true`
* `#[2, 4, 5, 6].all (· % 2 = 0) = false`
-/
@[inline]
def all (as : Array α) (p : α → Bool) (start := 0) (stop := as.size) : Bool :=
  Id.run <| as.allM p start stop

/--
Checks whether `a` is an element of `as`, using `==` to compare elements.

`Array.elem` is a synonym that takes the element before the array.

Examples:
* `#[1, 4, 2, 3, 3, 7].contains 3 = true`
* `Array.contains #[1, 4, 2, 3, 3, 7] 5 = false`
-/
def contains [BEq α] (as : Array α) (a : α) : Bool :=
  as.any (a == ·)

/--
Checks whether `a` is an element of `as`, using `==` to compare elements.

`Array.contains` is a synonym that takes the array before the element.

For verification purposes, `Array.elem` is simplified to `Array.contains`.

Example:
* `Array.elem 3 #[1, 4, 2, 3, 3, 7] = true`
* `Array.elem 5 #[1, 4, 2, 3, 3, 7] = false`
-/
def elem [BEq α] (a : α) (as : Array α) : Bool :=
  as.contains a

/-- Convert a `Array α` into an `List α`. This is O(n) in the size of the array.  -/
-- This function is exported to C, where it is called by `Array.toList`
-- (the projection) to implement this functionality.
@[export lean_array_to_list_impl]
def toListImpl (as : Array α) : List α :=
  as.foldr List.cons []

/--
Prepends an array to a list. The elements of the array are at the beginning of the resulting list.

Equivalent to `as.toList ++ l`.

Examples:
* `#[1, 2].toListAppend [3, 4] = [1, 2, 3, 4]`
* `#[1, 2].toListAppend [] = [1, 2]`
* `#[].toListAppend [3, 4, 5] = [3, 4, 5]`
-/
@[inline]
def toListAppend (as : Array α) (l : List α) : List α :=
  as.foldr List.cons l

/--
Appends two arrays. Normally used via the `++` operator.

Appending arrays takes time proportional to the length of the second array.

Examples:
  * `#[1, 2, 3] ++ #[4, 5] = #[1, 2, 3, 4, 5]`.
  * `#[] ++ #[4, 5] = #[4, 5]`.
  * `#[1, 2, 3] ++ #[] = #[1, 2, 3]`.
-/
protected def append (as : Array α) (bs : Array α) : Array α :=
  bs.foldl (init := as) fun xs v => xs.push v

instance : Append (Array α) := ⟨Array.append⟩

/--
Appends an array and a list.

Takes time proportional to the length of the list..

Examples:
  * `#[1, 2, 3].appendList [4, 5] = #[1, 2, 3, 4, 5]`.
  * `#[].appendList [4, 5] = #[4, 5]`.
  * `#[1, 2, 3].appendList [] = #[1, 2, 3]`.
-/
protected def appendList (as : Array α) (bs : List α) : Array α :=
  bs.foldl (init := as) fun xs v => xs.push v

instance : HAppend (Array α) (List α) (Array α) := ⟨Array.appendList⟩


/--
Applies a monadic function that returns an array to each element of an array, from left to right.
The resulting arrays are appended.
-/
@[inline]
def flatMapM [Monad m] (f : α → m (Array β)) (as : Array α) : m (Array β) :=
  as.foldlM (init := empty) fun bs a => do return bs ++ (← f a)

@[deprecated flatMapM (since := "2024-10-16")] abbrev concatMapM := @flatMapM

/--
Applies a function that returns an array to each element of an array. The resulting arrays are
appended.

Examples:
* `#[2, 3, 2].flatMap Array.range = #[0, 1, 0, 1, 2, 0, 1]`
* `#[['a', 'b'], ['c', 'd', 'e']].flatMap List.toArray = #['a', 'b', 'c', 'd', 'e']`
-/
@[inline]
def flatMap (f : α → Array β) (as : Array α) : Array β :=
  as.foldl (init := empty) fun bs a => bs ++ f a

@[deprecated flatMap (since := "2024-10-16")] abbrev concatMap := @flatMap

/--
Appends the contents of array of arrays into a single array. The resulting array contains the same
elements as the nested arrays in the same order.

Examples:
 * `#[#[5], #[4], #[3, 2]].flatten = #[5, 4, 3, 2]`
 * `#[#[0, 1], #[], #[2], #[1, 0, 1]].flatten = #[0, 1, 2, 1, 0, 1]`
 * `(#[] : Array Nat).flatten = #[]`
-/
@[inline] def flatten (xss : Array (Array α)) : Array α :=
  xss.foldl (init := empty) fun acc xs => acc ++ xs

/--
Reverses an array by repeatedly swapping elements.

The original array is modified in place if there are no other references to it.

Examples:
* `(#[] : Array Nat).reverse = #[]`
* `#[0, 1].reverse = #[1, 0]`
* `#[0, 1, 2].reverse = #[2, 1, 0]`
-/
def reverse (as : Array α) : Array α :=
  if h : as.size ≤ 1 then
    as
  else
    loop as 0 ⟨as.size - 1, Nat.pred_lt (mt (fun h : as.size = 0 => h ▸ by decide) h)⟩
where
  termination {i j : Nat} (h : i < j) : j - 1 - (i + 1) < j - i := by
    rw [Nat.sub_sub, Nat.add_comm]
    exact Nat.lt_of_le_of_lt (Nat.pred_le _) (Nat.sub_succ_lt_self _ _ h)
  loop (as : Array α) (i : Nat) (j : Fin as.size) :=
    if h : i < j then
      have := termination h
      let as := as.swap i j (Nat.lt_trans h j.2)
      have : j-1 < as.size := by rw [size_swap]; exact Nat.lt_of_le_of_lt (Nat.pred_le _) j.2
      loop as (i+1) ⟨j-1, this⟩
    else
      as

/--
Returns the array of elements in `as` for which `p` returns `true`.

Only elements from `start` (inclusive) to `stop` (exclusive) are considered. Elements outside that
range are discarded. By default, the entire array is considered.

Examples:
* `#[1, 2, 5, 2, 7, 7].filter (· > 2) = #[5, 7, 7]`
* `#[1, 2, 5, 2, 7, 7].filter (fun _ => false) = #[]`
* `#[1, 2, 5, 2, 7, 7].filter (fun _ => true) = #[1, 2, 5, 2, 7, 7]`
* `#[1, 2, 5, 2, 7, 7].filter (· > 2) (start := 3) = #[7, 7]`
* `#[1, 2, 5, 2, 7, 7].filter (fun _ => true) (start := 3) = #[2, 7, 7]`
* `#[1, 2, 5, 2, 7, 7].filter (fun _ => true) (stop := 3) = #[1, 2, 5]`
-/
@[inline]
def filter (p : α → Bool) (as : Array α) (start := 0) (stop := as.size) : Array α :=
  as.foldl (init := #[]) (start := start) (stop := stop) fun acc a =>
    if p a then acc.push a else acc

/--
Applies the monadic predicate `p` to every element in the array, in order from left to right, and
returns the array of elements for which `p` returns `true`.

Only elements from `start` (inclusive) to `stop` (exclusive) are considered. Elements outside that
range are discarded. By default, the entire array is checked.

Example:
```lean example
#eval #[1, 2, 5, 2, 7, 7].filterM fun x => do
  IO.println s!"Checking {x}"
  return x < 3
```
```output
Checking 1
Checking 2
Checking 5
Checking 2
Checking 7
Checking 7
```
```output
#[1, 2, 2]
```
-/
@[inline]
def filterM {α : Type} [Monad m] (p : α → m Bool) (as : Array α) (start := 0) (stop := as.size) : m (Array α) :=
  as.foldlM (init := #[]) (start := start) (stop := stop) fun acc a => do
    if (← p a) then return acc.push a else return acc

/--
Applies the monadic predicate `p` on every element in the array in reverse order, from right to
left, and returns those elements for which `p` returns `true`. The elements of the returned list are
in the same order as in the input list.

Only elements from `start` (exclusive) to `stop` (inclusive) are considered. Elements outside that
range are discarded. Because the array is examined in reverse order, elements are only examined when
`start > stop`. By default, the entire array is considered.

Example:
```lean example
#eval #[1, 2, 5, 2, 7, 7].filterRevM fun x => do
  IO.println s!"Checking {x}"
  return x < 3
```
```output
Checking 7
Checking 7
Checking 2
Checking 5
Checking 2
Checking 1
```
```output
#[1, 2, 2]
```
-/
@[inline]
def filterRevM {α : Type} [Monad m] (p : α → m Bool) (as : Array α) (start := as.size) (stop := 0) : m (Array α) :=
  reverse <$> as.foldrM (init := #[]) (start := start) (stop := stop) fun a acc => do
    if (← p a) then return acc.push a else return acc

/--
Applies a monadic function that returns an `Option` to each element of an array, collecting the
non-`none` values.

Only elements from `start` (inclusive) to `stop` (exclusive) are considered. Elements outside that
range are discarded. By default, the entire array is considered.

Example:
```lean example
#eval #[1, 2, 5, 2, 7, 7].filterMapM fun x => do
  IO.println s!"Examining {x}"
  if x > 2 then return some (2 * x)
  else return none
```
```output
Examining 1
Examining 2
Examining 5
Examining 2
Examining 7
Examining 7
```
```output
#[10, 14, 14]
```
-/
@[specialize]
def filterMapM [Monad m] (f : α → m (Option β)) (as : Array α) (start := 0) (stop := as.size) : m (Array β) :=
  as.foldlM (init := #[]) (start := start) (stop := stop) fun bs a => do
    match (← f a) with
    | some b => pure (bs.push b)
    | none   => pure bs

/--
Applies a function that returns an `Option` to each element of an array, collecting the non-`none`
values.

Example:
```lean example
#eval #[1, 2, 5, 2, 7, 7].filterMap fun x =>
  if x > 2 then some (2 * x) else none
```
```output
#[10, 14, 14]
```
-/
@[inline]
def filterMap (f : α → Option β) (as : Array α) (start := 0) (stop := as.size) : Array β :=
  Id.run <| as.filterMapM f (start := start) (stop := stop)

/--
Returns the largest element of the array, as determined by the comparison `lt`, or `none` if
the array is empty.

Examples:
* `(#[] : Array Nat).getMax? (· < ·) = none`
* `#["red", "green", "blue"].getMax? (·.length < ·.length) = some "green"`
* `#["red", "green", "blue"].getMax? (· < ·) = some "red"`
-/
@[specialize]
def getMax? (as : Array α) (lt : α → α → Bool) : Option α :=
  if h : 0 < as.size then
    let a0 := as[0]
    some <| as.foldl (init := a0) (start := 1) fun best a =>
      if lt best a then a else best
  else
    none

/--
Returns a pair of arrays that together contain all the elements of `as`. The first array contains
those elements for which `p` returns `true`, and the second contains those for which `p` returns
`false`.

`as.partition p` is equivalent to `(as.filter p, as.filter (not ∘ p))`, but it is
more efficient since it only has to do one pass over the array.

Examples:
 * `#[1, 2, 5, 2, 7, 7].partition (· > 2) = (#[5, 7, 7], #[1, 2, 2])`
 * `#[1, 2, 5, 2, 7, 7].partition (fun _ => false) = (#[], #[1, 2, 5, 2, 7, 7])`
 * `#[1, 2, 5, 2, 7, 7].partition (fun _ => true) = (#[1, 2, 5, 2, 7, 7], #[])`
-/
@[inline]
def partition (p : α → Bool) (as : Array α) : Array α × Array α := Id.run do
  let mut bs := #[]
  let mut cs := #[]
  for a in as do
    if p a then
      bs := bs.push a
    else
      cs := cs.push a
  return (bs, cs)

/--
Removes all the elements that satisfy a predicate from the end of an array.

The longest contiguous sequence of elements that all satisfy the predicate is removed.

Examples:
 * `#[0, 1, 2, 3, 4].popWhile (· > 2) = #[0, 1, 2]`
 * `#[3, 2, 3, 4].popWhile (· > 2) = #[3, 2]`
 * `(#[] : Array Nat).popWhile (· > 2) = #[]`
-/
@[semireducible] -- This is otherwise irreducible because it uses well-founded recursion.
def popWhile (p : α → Bool) (as : Array α) : Array α :=
  if h : as.size > 0 then
    if p (as[as.size - 1]'(Nat.sub_lt h (by decide))) then
      popWhile p as.pop
    else
      as
  else
    as
decreasing_by simp_wf; decreasing_trivial_pre_omega

@[simp] theorem popWhile_empty {p : α → Bool} :
    popWhile p #[] = #[] := by
  simp [popWhile]

/--
Returns a new array that contains the longest prefix of elements that satisfy the predicate `p` from
an array.

Examples:
 * `#[0, 1, 2, 3, 2, 1].takeWhile (· < 2) = #[0, 1]`
 * `#[0, 1, 2, 3, 2, 1].takeWhile (· < 20) = #[0, 1, 2, 3, 2, 1]`
 * `#[0, 1, 2, 3, 2, 1].takeWhile (· < 0) = #[]`
-/
def takeWhile (p : α → Bool) (as : Array α) : Array α :=
  let rec @[semireducible] -- This is otherwise irreducible because it uses well-founded recursion.
  go (i : Nat) (acc : Array α) : Array α :=
    if h : i < as.size then
      let a := as[i]
      if p a then
        go (i+1) (acc.push a)
      else
        acc
    else
      acc
    decreasing_by simp_wf; decreasing_trivial_pre_omega
  go 0 #[]

/--
Removes the element at a given index from an array without a run-time bounds check.

This function takes worst-case `O(n)` time because it back-shifts all elements at positions
greater than `i`.

Examples:
* `#["apple", "pear", "orange"].eraseIdx 0 = #["pear", "orange"]`
* `#["apple", "pear", "orange"].eraseIdx 1 = #["apple", "orange"]`
* `#["apple", "pear", "orange"].eraseIdx 2 = #["apple", "pear"]`
-/
@[semireducible] -- This is otherwise irreducible because it uses well-founded recursion.
def eraseIdx (xs : Array α) (i : Nat) (h : i < xs.size := by get_elem_tactic) : Array α :=
  if h' : i + 1 < xs.size then
    let xs' := xs.swap (i + 1) i
    xs'.eraseIdx (i + 1) (by simp [xs', h'])
  else
    xs.pop
termination_by xs.size - i
decreasing_by simp_wf; exact Nat.sub_succ_lt_self _ _ h

-- This is required in `Lean.Data.PersistentHashMap`.
@[simp] theorem size_eraseIdx {xs : Array α} (i : Nat) (h) : (xs.eraseIdx i h).size = xs.size - 1 := by
  induction xs, i, h using Array.eraseIdx.induct with
  | @case1 xs i h h' xs' ih =>
    unfold eraseIdx
    simp +zetaDelta [h', xs', ih]
  | case2 xs i h h' =>
    unfold eraseIdx
    simp [h']

/--
Removes the element at a given index from an array. Does nothing if the index is out of bounds.

This function takes worst-case `O(n)` time because it back-shifts all elements at positions greater
than `i`.

Examples:
* `#["apple", "pear", "orange"].eraseIdxIfInBounds 0 = #["pear", "orange"]`
* `#["apple", "pear", "orange"].eraseIdxIfInBounds 1 = #["apple", "orange"]`
* `#["apple", "pear", "orange"].eraseIdxIfInBounds 2 = #["apple", "pear"]`
* `#["apple", "pear", "orange"].eraseIdxIfInBounds 3 = #["apple", "pear", "orange"]`
* `#["apple", "pear", "orange"].eraseIdxIfInBounds 5 = #["apple", "pear", "orange"]`
-/
def eraseIdxIfInBounds (xs : Array α) (i : Nat) : Array α :=
  if h : i < xs.size then xs.eraseIdx i h else xs

/--
Removes the element at a given index from an array. Panics if the index is out of bounds.

This function takes worst-case `O(n)` time because it back-shifts all elements at positions
greater than `i`.
-/
def eraseIdx! (xs : Array α) (i : Nat) : Array α :=
  if h : i < xs.size then xs.eraseIdx i h else panic! "invalid index"

/--
Removes the first occurrence of a specified element from an array, or does nothing if it is not
present.

This function takes worst-case `O(n)` time because it back-shifts all later elements.

Examples:
* `#[1, 2, 3].erase 2 = #[1, 3]`
* `#[1, 2, 3].erase 5 = #[1, 2, 3]`
* `#[1, 2, 3, 2, 1].erase 2 = #[1, 3, 2, 1]`
* `(#[] : List Nat).erase 2 = #[]`
-/
def erase [BEq α] (as : Array α) (a : α) : Array α :=
  match as.finIdxOf? a with
  | none   => as
  | some i => as.eraseIdx i

/--
Removes the first element that satisfies the predicate `p`. If no element satisfies `p`, the array
is returned unmodified.

This function takes worst-case `O(n)` time because it back-shifts all later elements.

Examples:
* `#["red", "green", "", "blue"].eraseP (·.isEmpty) = #["red", "green", "blue"]`
* `#["red", "green", "", "blue", ""].eraseP (·.isEmpty) = #["red", "green", "blue", ""]`
* `#["red", "green", "blue"].eraseP (·.length % 2 == 0) = #["red", "green"]`
* `#["red", "green", "blue"].eraseP (fun _ => true) = #["green", "blue"]`
* `(#[] : Array String).eraseP (fun _ => true) = #[]`
-/
def eraseP (as : Array α) (p : α → Bool) : Array α :=
  match as.findFinIdx? p with
  | none   => as
  | some i => as.eraseIdx i

/--
Inserts an element into an array at the specified index. If the index is greater than the size of
the array, then the array is returned unmodified.

In other words, the new element is inserted into the array `as` after the first `i` elements of
`as`.

This function takes worst case `O(n)` time because it has to swap the inserted element into place.

Examples:
 * `#["tues", "thur", "sat"].insertIdx 1 "wed" = #["tues", "wed", "thur", "sat"]`
 * `#["tues", "thur", "sat"].insertIdx 2 "wed" = #["tues", "thur", "wed", "sat"]`
 * `#["tues", "thur", "sat"].insertIdx 3 "wed" = #["tues", "thur", "sat", "wed"]`
-/
@[inline] def insertIdx (as : Array α) (i : Nat) (a : α) (_ : i ≤ as.size := by get_elem_tactic) : Array α :=
  let rec @[semireducible] -- This is otherwise irreducible because it uses well-founded recursion.
  loop (as : Array α) (j : Fin as.size) :=
    if i < j then
      let j' : Fin as.size := ⟨j-1, Nat.lt_of_le_of_lt (Nat.pred_le _) j.2⟩
      let as := as.swap j' j
      loop as ⟨j', by rw [size_swap]; exact j'.2⟩
    else
      as
    decreasing_by simp_wf; decreasing_trivial_pre_omega
  let j := as.size
  let as := as.push a
  loop as ⟨j, size_push .. ▸ j.lt_succ_self⟩

@[deprecated insertIdx (since := "2024-11-20")] abbrev insertAt := @insertIdx

/--
Inserts an element into an array at the specified index. Panics if the index is greater than the
size of the array.

In other words, the new element is inserted into the array `as` after the first `i` elements of
`as`.

This function takes worst case `O(n)` time because it has to swap the inserted element into place.
`Array.insertIdx` and `Array.insertIdxIfInBounds` are safer alternatives.

Examples:
 * `#["tues", "thur", "sat"].insertIdx! 1 "wed" = #["tues", "wed", "thur", "sat"]`
 * `#["tues", "thur", "sat"].insertIdx! 2 "wed" = #["tues", "thur", "wed", "sat"]`
 * `#["tues", "thur", "sat"].insertIdx! 3 "wed" = #["tues", "thur", "sat", "wed"]`
-/
def insertIdx! (as : Array α) (i : Nat) (a : α) : Array α :=
  if h : i ≤ as.size then
    insertIdx as i a
  else panic! "invalid index"

@[deprecated insertIdx! (since := "2024-11-20")] abbrev insertAt! := @insertIdx!

/--
Inserts an element into an array at the specified index. The array is returned unmodified if the
index is greater than the size of the array.

In other words, the new element is inserted into the array `as` after the first `i` elements of
`as`.

This function takes worst case `O(n)` time because it has to swap the inserted element into place.

Examples:
 * `#["tues", "thur", "sat"].insertIdxIfInBounds 1 "wed" = #["tues", "wed", "thur", "sat"]`
 * `#["tues", "thur", "sat"].insertIdxIfInBounds 2 "wed" = #["tues", "thur", "wed", "sat"]`
 * `#["tues", "thur", "sat"].insertIdxIfInBounds 3 "wed" = #["tues", "thur", "sat", "wed"]`
 * `#["tues", "thur", "sat"].insertIdxIfInBounds 4 "wed" = #["tues", "thur", "sat"]`
-/
def insertIdxIfInBounds (as : Array α) (i : Nat) (a : α) : Array α :=
  if h : i ≤ as.size then
    insertIdx as i a
  else
    as

@[semireducible] -- This is otherwise irreducible because it uses well-founded recursion.
def isPrefixOfAux [BEq α] (as bs : Array α) (hle : as.size ≤ bs.size) (i : Nat) : Bool :=
  if h : i < as.size then
    let a := as[i]
    have : i < bs.size := Nat.lt_of_lt_of_le h hle
    let b := bs[i]
    if a == b then
      isPrefixOfAux as bs hle (i+1)
    else
      false
  else
    true
decreasing_by simp_wf; decreasing_trivial_pre_omega

/--
Return `true` if `as` is a prefix of `bs`, or `false` otherwise.

Examples:
 * `#[0, 1, 2].isPrefixOf #[0, 1, 2, 3] = true`
 * `#[0, 1, 2].isPrefixOf #[0, 1, 2] = true`
 * `#[0, 1, 2].isPrefixOf #[0, 1] = false`
 * `#[].isPrefixOf #[0, 1] = true`
-/
def isPrefixOf [BEq α] (as bs : Array α) : Bool :=
  if h : as.size ≤ bs.size then
    isPrefixOfAux as bs h 0
  else
    false

@[semireducible, specialize] -- This is otherwise irreducible because it uses well-founded recursion.
def zipWithAux (as : Array α) (bs : Array β) (f : α → β → γ) (i : Nat) (cs : Array γ) : Array γ :=
  if h : i < as.size then
    let a := as[i]
    if h : i < bs.size then
      let b := bs[i]
      zipWithAux as bs f (i+1) <| cs.push <| f a b
    else
      cs
  else
    cs
decreasing_by simp_wf; decreasing_trivial_pre_omega

/--
Applies a function to the corresponding elements of two arrays, stopping at the end of the shorter
array.

Examples:
* `#[1, 2].zipWith (· + ·) #[5, 6] = #[6, 8]`
* `#[1, 2, 3].zipWith (· + ·) #[5, 6, 10] = #[6, 8, 13]`
* `#[].zipWith (· + ·) #[5, 6] = #[]`
* `#[x₁, x₂, x₃].zipWith f #[y₁, y₂, y₃, y₄] = #[f x₁ y₁, f x₂ y₂, f x₃ y₃]`
-/
@[inline] def zipWith (f : α → β → γ) (as : Array α) (bs : Array β) : Array γ :=
  zipWithAux as bs f 0 #[]

/--
Combines two arrays into an array of pairs in which the first and second components are the
corresponding elements of each input array. The resulting array is the length of the shorter of the
input arrays.

Examples:
* `#["Mon", "Tue", "Wed"].zip #[1, 2, 3] = #[("Mon", 1), ("Tue", 2), ("Wed", 3)]`
* `#["Mon", "Tue", "Wed"].zip #[1, 2] = #[("Mon", 1), ("Tue", 2)]`
* `#[x₁, x₂, x₃].zip #[y₁, y₂, y₃, y₄] = #[(x₁, y₁), (x₂, y₂), (x₃, y₃)]`
-/
def zip (as : Array α) (bs : Array β) : Array (α × β) :=
  zipWith Prod.mk as bs

/--
Applies a function to the corresponding elements of both arrays, stopping when there are no more
elements in either array. If one array is shorter than the other, the function is passed `none` for
the missing elements.

Examples:
* `#[1, 6].zipWithAll min #[5, 2] = #[some 1, some 2]`
* `#[1, 2, 3].zipWithAll Prod.mk #[5, 6] = #[(some 1, some 5), (some 2, some 6), (some 3, none)]`
* `#[x₁, x₂].zipWithAll f #[y] = #[f (some x₁) (some y), f (some x₂) none]`
-/
def zipWithAll (f : Option α → Option β → γ) (as : Array α) (bs : Array β) : Array γ :=
  go as bs 0 #[]
where go (as : Array α) (bs : Array β) (i : Nat) (cs : Array γ) :=
  if i < max as.size bs.size then
    let a := as[i]?
    let b := bs[i]?
    go as bs (i+1) (cs.push (f a b))
  else
    cs
  termination_by max as.size bs.size - i
  decreasing_by simp_wf; decreasing_trivial_pre_omega

/--
Separates an array of pairs into two arrays that contain the respective first and second components.

Examples:
* `#[("Monday", 1), ("Tuesday", 2)].unzip = (#["Monday", "Tuesday"], #[1, 2])`
* `#[(x₁, y₁), (x₂, y₂), (x₃, y₃)].unzip = (#[x₁, x₂, x₃], #[y₁, y₂, y₃])`
* `(#[] : Array (Nat × String)).unzip = ((#[], #[]) : List Nat × List String)`
-/
def unzip (as : Array (α × β)) : Array α × Array β :=
  as.foldl (init := (#[], #[])) fun (as, bs) (a, b) => (as.push a, bs.push b)

@[deprecated partition (since := "2024-11-06")]
def split (as : Array α) (p : α → Bool) : Array α × Array α :=
  as.foldl (init := (#[], #[])) fun (as, bs) a =>
    if p a then (as.push a, bs) else (as, bs.push a)

/--
Replaces the first occurrence of `a` with `b` in an array. The modification is performed in-place
when the reference to the array is unique. Returns the array unmodified when `a` is not present.

Examples:
* `#[1, 2, 3, 2, 1].replace 2 5 = #[1, 5, 3, 2, 1]`
* `#[1, 2, 3, 2, 1].replace 0 5 = #[1, 2, 3, 2, 1]`
* `#[].replace 2 5 = #[]`
-/
def replace [BEq α] (xs : Array α) (a b : α) : Array α :=
  match xs.finIdxOf? a with
  | none => xs
  | some i => xs.set i b

/-! ### Lexicographic ordering -/

instance instLT [LT α] : LT (Array α) := ⟨fun as bs => as.toList < bs.toList⟩
instance instLE [LT α] : LE (Array α) := ⟨fun as bs => as.toList ≤ bs.toList⟩

-- See `Init.Data.Array.Lex.Basic` for the boolean valued lexicographic comparator.

/-! ## Auxiliary functions used in metaprogramming.

We do not currently intend to provide verification theorems for these functions.
-/

/-! ### leftpad and rightpad -/

/--
Pads `xs : Array α` on the left with repeated occurrences of `a : α` until it is of size `n`. If `xs`
already has at least `n` elements, it is returned unmodified.

Examples:
 * `#[1, 2, 3].leftpad 5 0 = #[0, 0, 1, 2, 3]`
 * `#["red", "green", "blue"].leftpad 4 "blank" = #["blank", "red", "green", "blue"]`
 * `#["red", "green", "blue"].leftpad 3 "blank" = #["red", "green", "blue"]`
 * `#["red", "green", "blue"].leftpad 1 "blank" = #["red", "green", "blue"]`
-/
def leftpad (n : Nat) (a : α) (xs : Array α) : Array α := replicate (n - xs.size) a ++ xs

/--
Pads `xs : Array α` on the right with repeated occurrences of `a : α` until it is of length `n`. If
`l` already has at least `n` elements, it is returned unmodified.

Examples:
 * `#[1, 2, 3].rightpad 5 0 = #[1, 2, 3, 0, 0]`
 * `#["red", "green", "blue"].rightpad 4 "blank" = #["red", "green", "blue", "blank"]`
 * `#["red", "green", "blue"].rightpad 3 "blank" = #["red", "green", "blue"]`
 * `#["red", "green", "blue"].rightpad 1 "blank" = #["red", "green", "blue"]`
-/
def rightpad (n : Nat) (a : α) (xs : Array α) : Array α := xs ++ replicate (n - xs.size) a

/- ### reduceOption -/

/-- Drop `none`s from a Array, and replace each remaining `some a` with `a`. -/
@[inline] def reduceOption (as : Array (Option α)) : Array α :=
  as.filterMap id

/-! ### eraseReps -/

/--
Erases repeated elements, keeping the first element of each run.

`O(|as|)`.

Example:
* `#[1, 3, 2, 2, 2, 3, 3, 5].eraseReps = #[1, 3, 2, 3, 5]`
-/
def eraseReps {α} [BEq α] (as : Array α) : Array α :=
  if h : 0 < as.size then
    let ⟨last, acc⟩ := as.foldl (init := (as[0], #[])) fun ⟨last, acc⟩ a =>
      if a == last then ⟨last, acc⟩ else ⟨a, acc.push last⟩
    acc.push last
  else
    #[]

/-! ### allDiff -/

private def allDiffAuxAux [BEq α] (as : Array α) (a : α) : forall (i : Nat), i < as.size → Bool
  | 0,   _ => true
  | i+1, h =>
    have : i < as.size := Nat.lt_trans (Nat.lt_succ_self _) h;
    a != as[i] && allDiffAuxAux as a i this

@[semireducible] -- This is otherwise irreducible because it uses well-founded recursion.
private def allDiffAux [BEq α] (as : Array α) (i : Nat) : Bool :=
  if h : i < as.size then
    allDiffAuxAux as as[i] i h && allDiffAux as (i+1)
  else
    true
decreasing_by simp_wf; decreasing_trivial_pre_omega

/--
Returns `true` if no two elements of `as` are equal according to the `==` operator.

Examples:
 * `#["red", "green", "blue"].allDiff = true`
 * `#["red", "green", "red"].allDiff = false`
 * `(#[] : Array Nat).allDiff = true`
-/
def allDiff [BEq α] (as : Array α) : Bool :=
  allDiffAux as 0

/-! ### getEvenElems -/

/--
Returns a new array that contains the elements at even indices in `as`, starting with the element at
index `0`.

Examples:
* `#[0, 1, 2, 3, 4].getEvenElems = #[0, 2, 4]`
* `#[1, 2, 3, 4].getEvenElems = #[1, 3]`
* `#["red", "green", "blue"].getEvenElems = #["red", "blue"]`
* `(#[] : Array String).getEvenElems = #[]`
-/
@[inline] def getEvenElems (as : Array α) : Array α :=
  (·.2) <| as.foldl (init := (true, Array.empty)) fun (even, acc) a =>
    if even then
      (false, acc.push a)
    else
      (true, acc)

/-! ### Repr and ToString -/

instance {α : Type u} [Repr α] : Repr (Array α) where
  reprPrec xs _ :=
    let _ : Std.ToFormat α := ⟨repr⟩
    if xs.size == 0 then
      "#[]"
    else
      Std.Format.bracketFill "#[" (Std.Format.joinSep (toList xs) ("," ++ Std.Format.line)) "]"

instance [ToString α] : ToString (Array α) where
  toString xs := "#" ++ toString xs.toList

end Array

export Array (mkArray)
