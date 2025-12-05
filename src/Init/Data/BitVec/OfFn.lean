/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fady Adal
-/
module

prelude
public import Init.Data.BitVec.Basic
public import Init.Data.BitVec.Folds
public import Init.Data.List.Basic
public import Init.Data.Array.Basic
public import Init.Data.Array.Lemmas
public import Init.Data.Array.OfFn
public import Init.Data.Function
public import Init.Data.Vector.Basic
public import Init.Data.Vector.Lemmas
public import Init.Data.BitVec.Lemmas

public section

set_option linter.missingDocs true

namespace BitVec

/-!
## Conversion functions

This module provides conversions between `BitVec` and other container types
(`List`, `Array`, `Vector`), as well as construction from functions.

These functions treat bitvectors as containers of bits, ordered from least
significant (index 0) to most significant (index w-1).
-/

/--
Build a bitvector from a function on indices.

The function `f` is called with indices from 0 to w-1, and the resulting
bits are assembled into the bitvector with `f 0` as the least significant bit.

Examples:
* `ofFn (fun i => i.val % 2 == 0) : BitVec 4 = 0b0101#4`
* `ofFn (fun _ => true) : BitVec 3 = 0b111#3`
-/
def ofFn (f : Fin w → Bool) : BitVec w :=
  (iunfoldr (fun i _ => ((), f i)) ()).snd

@[simp, grind =]
theorem ofFn_nil (f : Fin 0 → Bool) : ofFn f = nil := by
  ext
  contradiction


theorem getElem_ofFn (f : Fin w → Bool) (i : Nat) (h : i < w) :
    (ofFn f)[i] = f ⟨i, h⟩ := by
  unfold ofFn
  rw [←getLsbD_eq_getElem, iunfoldr_getLsbD (fun i => ()) ⟨i, h⟩]
  simp


@[simp]
theorem getLsbD_ofFn (f : Fin w → Bool) (i : Nat) :
    (ofFn f).getLsbD i = if h : i < w then f ⟨i, h⟩ else false := by
  by_cases h : i < w
  · simp [h, getElem_ofFn]
  · simp only [h, ↓reduceDIte]
    exact getLsbD_of_ge _ _ (by omega)

/--
Convert a bitvector to a list of bools (LSB first).

The resulting list has the least significant bit at index 0.

Examples:
* `(0b1010#4).toList = [false, true, false, true]`
* `(0#3).toList = [false, false, false]`
-/
def toList (x : BitVec w) : List Bool :=
  List.ofFn (n := w) (fun i => x[i])

@[simp, grind =]
theorem length_toList (x : BitVec w) : x.toList.length = w := by
  simp [toList]

@[simp, grind =]
theorem getElem_toList (x : BitVec w) (i : Nat) (h : i < x.toList.length) :
    x.toList[i] = x[i]'(by simpa using h) := by
  simp [toList]

theorem toList_injective : Function.Injective (toList (w := w)) := by
  intro x y h
  ext i
  have : x.toList[i]'(by simpa) = y.toList[i]'(by simpa) := by
    simp [h]
  simpa using this

@[simp]
theorem toList_inj {x y : BitVec w} : x.toList = y.toList ↔ x = y :=
  toList_injective.eq_iff

@[simp]
theorem toList_nil : toList nil = [] := by
  simp [toList]

@[simp]
theorem toList_cons (b : Bool) (x : BitVec w) :
    toList (cons b x) = (toList x).concat b := by
  simp only [List.concat_eq_append]
  ext i bi
  by_cases h : i < w + 1
  · repeat rw [List.getElem?_eq_getElem (by simpa)]
    simp only [Option.some.injEq]
    rw [getElem_toList, getElem_cons]
    by_cases h' : i = w
    · rwa [dif_pos, List.getElem_concat_length (by simpa)]
    · rw [dif_neg h', List.getElem_append_left (by simp only [length_toList]; omega),
          getElem_toList]

  · repeat rw [List.getElem?_eq_none (by
      simp only [List.length_append, length_toList,
                 List.length_cons, List.length_nil, Nat.zero_add];
      omega
    )]

@[simp]
theorem toList_concat (x : BitVec w) (b : Bool) :
    toList (concat x b) = b :: toList x := by
  ext i
  by_cases h : i < w + 1
  · repeat rw [List.getElem?_eq_getElem (by simpa)]
    simp only [Option.some.injEq, List.getElem_cons]
    rw [getElem_toList, getElem_concat]
    cases i <;> simp
  · repeat rw [List.getElem?_eq_none (by simp only [List.length_cons, length_toList]; omega)]

/--
Convert a bitvector to a list of bools (MSB first).

The resulting list has the most significant bit at index 0.

Examples:
* `(0b1010#4).toListBE = [true, false, true, false]`
* `(0#3).toListBE = [false, false, false]`
-/
def toListBE (x : BitVec w) : List Bool :=
  List.ofFn (n := w) (fun i => x[w - i - 1])


@[simp, grind =]
theorem length_toListBE (x : BitVec w) : x.toListBE.length = w := by
  simp [toListBE]

@[simp, grind =]
theorem getElem_toListBE (x : BitVec w) (i : Nat) (h : i < x.toListBE.length) :
    x.toListBE[i] = x[w - i - 1]'(by simp only [length_toListBE] at h; omega) := by
  simp [toListBE]

theorem toListBE_injective : Function.Injective (toListBE (w := w)) := by
  intro x y h
  ext i
  have : x.toListBE[w - i - 1]'(by simp only [length_toListBE]; omega) = y.toListBE[w - i - 1]'(by simp only [length_toListBE]; omega) := by
    simp [h]
  have weq : w - (w - i - 1) - 1 = i := by omega
  simpa [getElem_toListBE, weq] using this

@[simp]
theorem toListBE_inj {x y : BitVec w} : x.toListBE = y.toListBE ↔ x = y :=
  toListBE_injective.eq_iff

@[simp]
theorem toListBE_nil : toListBE nil = [] := by
  simp [toListBE]

@[simp]
theorem toListBE_cons (b : Bool) (x : BitVec w) :
    toListBE (cons b x) = b :: toListBE x := by
  ext i bi
  by_cases h : i < w + 1
  · repeat rw [List.getElem?_eq_getElem (by simpa)]
    simp only [Option.some.injEq]
    rw [getElem_toListBE, getElem_cons]
    cases i with
    | zero => simp
    | succ i' =>
      rw [dif_neg]
      simp only [Nat.reduceSubDiff, List.getElem_cons_succ, getElem_toListBE]
      omega
  · repeat rw [List.getElem?_eq_none (by simp only [List.length_cons, length_toListBE]; omega)]

@[simp]
theorem toListBE_concat (b : Bool) (x : BitVec w) :
    toListBE (concat x b) = toListBE x ++ [b] := by
  ext i bi
  by_cases h : i < w + 1
  · repeat rw [List.getElem?_eq_getElem (by simpa)]
    simp only [getElem_toListBE, Option.some.injEq]
    by_cases h' : i = w
    · repeat rw [List.getElem?_eq_getElem (by simp)]
      rw [getElem_concat, List.getElem_append_right (by simp only [length_toListBE]; omega), dif_pos (by omega)]
      simp
    · rw [getElem_concat, List.getElem_append_left (by simp; omega), dif_neg (by omega)]
      simp [show w + 1 - i - 1 - 1 = w - i - 1 by omega]
  · repeat rw [List.getElem?_eq_none (by simp; omega)]

/--
Round-trip: `ofBoolListLE` and `toList` are inverses.
-/
@[simp]
theorem toList_ofBoolListLE (l : List Bool) : (ofBoolListLE l).toList = l := by
  induction l with
  | nil => simp [ofBoolListLE, ←ofNat_eq_ofNat]
  | cons b bs ih => simp [ofBoolListLE, ih]

@[simp]
theorem toList_cast {w v : Nat} (h : w = v) (x : BitVec w) : (x.cast h).toList = x.toList := by
  subst h
  rfl

@[simp]
theorem cons_cast {w v : Nat} (h : w = v) (b : Bool) (x : BitVec w) :
    cons b (x.cast h) = (cons b x).cast (by simp [h]) := by
  subst h
  rfl

theorem ofBoolListLE_concat (l : List Bool) (b : Bool) :
    ofBoolListLE (l ++ [b]) = (cons b (ofBoolListLE l)).cast (by simp) := by
  apply toList_injective
  simp [toList_ofBoolListLE, toList_cons]

theorem ofBoolListLE_congr {l1 l2 : List Bool} (h : l1 = l2) :
    ofBoolListLE l1 = (ofBoolListLE l2).cast (by rw [h]) := by
  subst h
  rfl

/--
Round-trip: `toList` and `ofBoolListLE` are inverses.
-/
@[simp]
theorem ofBoolListLE_toList (x : BitVec w) : ofBoolListLE x.toList = x.cast (by simp) := by
  induction x using BitVec.induction with
  | nil => rfl
  | cons _ b x' ih =>
    calc ofBoolListLE (cons b x').toList
      _ = (ofBoolListLE ((toList x').concat b)).cast (by rw [toList_cons]) := by
        apply ofBoolListLE_congr
        exact toList_cons _ _
      _ = (cons b x').cast (by simp) := by
        rw [ofBoolListLE_congr List.concat_eq_append,
            ofBoolListLE_concat,
            ih]
        simp
/--
Round-trip: `ofBoolListBE` and `toListBE` are inverses.
-/
@[simp]
theorem toListBE_ofBoolListBE (l : List Bool) : (ofBoolListBE l).toListBE = l := by
  induction l with
  | nil => simp [ofBoolListBE, ←ofNat_eq_ofNat]
  | cons b bs ih => simp [ofBoolListBE, ih]

theorem ofBoolListBE_congr {l1 l2 : List Bool} (h : l1 = l2) :
    ofBoolListBE l1 = (ofBoolListBE l2).cast (by rw [h]) := by
  subst h
  rfl

theorem ofBoolListBE_cons (l : List Bool) (b : Bool) :
    ofBoolListBE (b :: l) = ((ofBoolListBE l).cons b).cast (by simp) := by
  apply toListBE_injective
  simp [toListBE_ofBoolListBE, toListBE_cons]

/--
Round-trip: `toListBE` and `ofBoolListBE` are inverses.
-/
@[simp]
theorem ofBoolListBE_toListBE (x : BitVec w) :
  ofBoolListBE x.toListBE = x.cast (by simp) := by
    induction x using BitVec.induction with
    | nil => rfl
    | cons w' b x' ih =>
      calc ofBoolListBE (cons b x').toListBE
        _ = (ofBoolListBE (b :: x'.toListBE)).cast (by rw [toListBE_cons]) := by
          apply ofBoolListBE_congr
          simp
        _ = (x'.cons b).cast (by simp) := by
          rw [ofBoolListBE_cons,
              ih]
          simp_all

/--
Convert a bitvector to an array of bools (LSB first).

The resulting array has the least significant bit at index 0.

Examples:
* `(0b1010#4).toArray = #[false, true, false, true]`
* `(0#3).toArray = #[false, false, false]`
-/
def toArray (x : BitVec w) : Array Bool :=
  Array.ofFn (n := w) (fun i => x[i])

@[simp, grind =]
theorem size_toArray (x : BitVec w) : x.toArray.size = w := by
  simp [toArray]

@[simp, grind =]
theorem getElem_toArray (x : BitVec w) (i : Nat) (h : i < x.toArray.size) :
    x.toArray[i] = x[i]'(by simpa using h) := by
  simp [toArray]

theorem toArray_injective : Function.Injective (toArray (w := w)) := by
  intro x y h
  ext i
  have : x.toArray[i]'(by simpa) = y.toArray[i]'(by simpa) := by
    simp [h]
  simpa using this

@[simp]
theorem toArray_inj {x y : BitVec w} : x.toArray = y.toArray ↔ x = y :=
  toArray_injective.eq_iff

@[simp]
theorem toList_toArray (x : BitVec w) : x.toArray.toList = x.toList := by
  ext i
  by_cases h : i < w
  · simp [h, toArray, toList]
  · repeat rw [List.getElem?_eq_none (by simp; omega)]

/--
Build a bitvector from an array of bools.

Takes the first `w` elements from the array. If the array is shorter than `w`,
the remaining bits are set to `false`.

Examples:
* `ofArray 4 #[false, true, false, true] = 0b1010#4`
* `ofArray 3 #[true, true] = 0b011#3` (padded with false)
* `ofArray 2 #[true, true, false, true] = 0b11#2` (truncated)
-/
def ofArray (w : Nat) (a : Array Bool) : BitVec w :=
  ofFn (fun i => a.getD i.val false)

theorem getElem_ofArray (w : Nat) (a : Array Bool) (i : Nat) (h : i < w) :
    (ofArray w a)[i] = a.getD i false := by
  simp [ofArray, getElem_ofFn]

@[simp]
theorem ofArray_toArray (x : BitVec w) : ofArray w x.toArray = x := by
  ext
  simp [ofArray, getElem_ofFn, toArray]

@[simp]
theorem toArray_ofArray (a : Array Bool) : (ofArray a.size a).toArray = a := by
  ext i; simp
  by_cases h : i < a.size
  · simp [toArray, ofArray, getElem_ofFn]
  · contradiction

@[simp]
theorem toArray_nil : toArray nil = #[] := by
  simp [toArray]

@[simp]
theorem toArray_concat (x : BitVec w) (b : Bool) :
    toArray (concat x b) = #[b] ++ toArray x := by
  apply Array.ext
  · simp; omega
  · intro i h
    simp only [size_toArray] at h
    simp only [getElem_toArray, getElem_concat (h := h)]
    split
    · simp_all
    · have : 1 <= i := by omega
      simp_all

theorem toArray_eq_toList_toArray (x : BitVec w) : x.toArray = x.toList.toArray := by
  ext i h₁ h₂ <;> simp

theorem toList_ofFn (f : Fin w → Bool) : (ofFn f).toList = List.ofFn f := by
  ext i
  by_cases h : i < w
  · repeat rw [List.getElem?_eq_getElem (by simpa)]
    simp [getElem_ofFn]
  · repeat rw [List.getElem?_eq_none (by simp; omega)]

theorem toArray_ofFn (f : Fin w → Bool) : (ofFn f).toArray = Array.ofFn f := by
  ext <;> simp [getElem_ofFn]

/--
Building a bitvector from its own indexing function is the identity.
-/
@[simp]
theorem ofFn_getElem (x : BitVec w) : ofFn (fun i => x[i]) = x := by
  ext i
  simp [getElem_ofFn]

/--
Convert a bitvector to a vector of bools (LSB first).

The resulting vector has the least significant bit at index 0.

Examples:
* `(0b1010#4).toVector = #v[false, true, false, true]`
* `(0#3).toVector = #v[false, false, false]`
-/
def toVector (x : BitVec w) : Vector Bool w :=
  ⟨x.toArray, by simp⟩

@[simp, grind =]
theorem toVector_toArray (x : BitVec w) : x.toVector.toArray = x.toArray := by
  simp [toVector]

theorem get_toVector (x : BitVec w) (i : Fin w) :
    x.toVector.get i = x[i.val] := by
  simp [toVector, Vector.get, toArray]

theorem toVector_injective : Function.Injective (toVector (w := w)) := by
  intro x y h
  have : x.toArray = y.toArray := by
    have := congrArg Vector.toArray h
    simpa using this
  exact toArray_injective this

@[simp]
theorem toVector_inj {x y : BitVec w} : x.toVector = y.toVector ↔ x = y :=
  toVector_injective.eq_iff

/--
Build a bitvector from a vector of bools.

The vector must have exactly `w` elements.

Examples:
* `ofVector #v[false, true, false, true] = 0b1010#4`
* `ofVector #v[true, true, true] = 0b111#3`
-/
def ofVector (v : Vector Bool w) : BitVec w :=
  ofArray w v.toArray

theorem getElem_ofVector (v : Vector Bool w) (i : Nat) (h : i < w) :
    (ofVector v)[i] = v.get ⟨i, h⟩ := by
  simp [ofVector, ofArray, getElem_ofFn, Vector.get]

@[simp]
theorem ofVector_toVector (x : BitVec w) : ofVector x.toVector = x := by
  simp [ofVector, toVector]

@[simp]
theorem toVector_ofVector (v : Vector Bool w) : (ofVector v).toVector = v := by
  rcases v with ⟨arr, rfl⟩
  simp [toVector, ofVector]

@[simp]
theorem toVector_nil : toVector nil = #v[] := by
  ext
  contradiction

@[simp]
theorem toVector_concat (x : BitVec w) (b : Bool) :
    toVector (concat x b) = Vector.mk (#[b] ++ x.toArray) (by simp +arith) := by
  apply Vector.ext
  intro i
  simp [toVector, Vector.getElem_mk]

theorem toList_toVector (x : BitVec w) : x.toVector.toList = x.toList := by
  simp [Vector.toList, toVector]

end BitVec
