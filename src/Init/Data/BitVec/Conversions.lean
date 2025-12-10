/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fady Adal
-/
module

prelude
public import Init.Data.Array.Basic
public import Init.Data.Array.Lemmas
public import Init.Data.Array.OfFn
public import Init.Data.BitVec.Basic
public import Init.Data.BitVec.Folds
public import Init.Data.BitVec.Lemmas
public import Init.Data.ByteArray.Basic
public import Init.Data.ByteArray.Lemmas
public import Init.Data.Function
public import Init.Data.List.Basic
public import Init.Data.Nat.Basic
public import Init.Data.UInt.Lemmas
public import Init.Data.Vector.Basic
public import Init.Data.Vector.Lemmas

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
* `ofFnLE (fun i => i.val % 2 == 0) : BitVec 4 = 0b0101#4`
* `ofFnLE (fun _ => true) : BitVec 3 = 0b111#3`
-/
def ofFnLE (f : Fin w → Bool) : BitVec w :=
  (iunfoldr (fun i _ => ((), f i)) ()).snd

@[simp, grind =]
theorem ofFnLE_nil (f : Fin 0 → Bool) : ofFnLE f = nil := by
  ext
  contradiction


@[simp]
theorem getElem_ofFnLE (f : Fin w → Bool) (i : Nat) (h : i < w) :
  (ofFnLE f)[i] = f ⟨i, h⟩ := by
    unfold ofFnLE
    rw [←getLsbD_eq_getElem, iunfoldr_getLsbD (fun i => ()) ⟨i, h⟩]
    simp


@[simp]
theorem getLsbD_ofFnLE (f : Fin w → Bool) (i : Nat) :
    (ofFnLE f).getLsbD i = if h : i < w then f ⟨i, h⟩ else false := by
  by_cases h : i < w
  · simp [h, getElem_ofFnLE]
  · rw [dif_neg h]
    exact getLsbD_of_ge _ _ (by omega)

/--
Build a bitvector from a function on indices (MSB first).

The function `f` is called with indices from 0 to w-1, and the resulting
bits are assembled into the bitvector with `f 0` as the most significant bit.

Examples:
* `ofFnBE (fun i => i.val % 2 == 0) : BitVec 4 = 0b1010#4`
* `ofFnBE (fun _ => true) : BitVec 3 = 0b111#3`
-/
def ofFnBE (f : Fin w → Bool) : BitVec w :=
  ofFnLE (fun i => f ⟨w - 1 - i, by omega⟩)

@[simp, grind =]
theorem ofFnBE_nil (f : Fin 0 → Bool) : ofFnBE f = nil := by
  ext
  contradiction

@[simp]
theorem getElem_ofFnBE (f : Fin w → Bool) (i : Nat) (h : i < w) :
  (ofFnBE f)[i] = f ⟨w - 1 - i, by omega⟩ := by
    simp [ofFnBE, getElem_ofFnLE]

@[simp]
theorem getLsbD_ofFnBE (f : Fin w → Bool) (i : Nat) :
    (ofFnBE f).getLsbD i = if h : i < w then f ⟨w - 1 - i, by omega⟩ else false := by
  by_cases h : i < w
  · simp [h, getElem_ofFnBE]
  · rw [dif_neg h]
    exact getLsbD_of_ge _ _ (by omega)

/--
Convert a bitvector to a list of bools (LSB first).

The resulting list has the least significant bit at index 0.

Examples:
* `(0b1010#4).toListLE = [false, true, false, true]`
* `(0#3).toListLE = [false, false, false]`
-/
def toListLE (x : BitVec w) : List Bool :=
  List.ofFn (n := w) (fun i => x[i])

@[simp, grind =]
theorem length_toListLE (x : BitVec w) : x.toListLE.length = w := by
  simp [toListLE]

@[simp, grind =]
theorem getElem_toListLE (x : BitVec w) (i : Nat) (h : i < x.toListLE.length) :
    x.toListLE[i] = x[i]'(by simpa using h) := by
  simp [toListLE]

@[simp, grind =]
theorem getElem?_toListLE (x : BitVec w) (i : Nat) :
    x.toListLE[i]? = x[i]? := by
  by_cases h : i < w <;> simp [h]

theorem toListLE_injective : Function.Injective (toListLE (w := w)) := by
  intro x y h
  ext i
  have : x.toListLE[i]'(by simpa) = y.toListLE[i]'(by simpa) := by
    simp [h]
  simpa using this

@[simp]
theorem toListLE_inj {x y : BitVec w} : x.toListLE = y.toListLE ↔ x = y :=
  toListLE_injective.eq_iff

@[simp]
theorem toListLE_nil : toListLE nil = [] := by
  simp [toListLE]

@[simp]
theorem toListLE_cons (b : Bool) (x : BitVec w) :
    toListLE (cons b x) = (toListLE x).concat b := by
  simp only [List.concat_eq_append]
  ext i bi
  by_cases h : i < w + 1
  · repeat rw [List.getElem?_eq_getElem (by simpa)]
    simp only [Option.some.injEq]
    rw [getElem_toListLE, getElem_cons]
    by_cases h' : i = w
    · rwa [dif_pos, List.getElem_concat_length (by simpa)]
    · rw [dif_neg h', List.getElem_append_left (by simp only [length_toListLE]; omega),
          getElem_toListLE]

  · repeat rw [List.getElem?_eq_none (by
      simp only [List.length_append, length_toListLE,
                 List.length_cons, List.length_nil, Nat.zero_add]
      omega
    )]

@[simp]
theorem toListLE_concat (x : BitVec w) (b : Bool) :
    toListLE (concat x b) = b :: toListLE x := by
  ext i
  by_cases h : i < w + 1
  · repeat rw [List.getElem?_eq_getElem (by simpa)]
    simp only [Option.some.injEq, List.getElem_cons]
    rw [getElem_toListLE, getElem_concat]
    cases i <;> simp
  · repeat rw [List.getElem?_eq_none (by simp only [List.length_cons, length_toListLE]; omega)]

/--
Convert a bitvector to a list of bools (MSB first).

The resulting list has the most significant bit at index 0.

Examples:
* `(0b1010#4).toListBE = [true, false, true, false]`
* `(0#3).toListBE = [false, false, false]`
-/
def toListBE (x : BitVec w) : List Bool :=
  List.ofFn (n := w) (fun i => x[w - 1 - i])


@[simp, grind =]
theorem length_toListBE (x : BitVec w) : x.toListBE.length = w := by
  simp [toListBE]

@[simp, grind =]
theorem getElem_toListBE (x : BitVec w) (i : Nat) (h : i < x.toListBE.length) :
    x.toListBE[i] = x[w - 1 - i]'(by simp only [length_toListBE] at h; omega) := by
  simp [toListBE]

@[simp, grind =]
theorem getElem?_toListBE (x : BitVec w) (i : Nat) (h : i < x.toListBE.length) :
  x.toListBE[i]? = x[w - 1 - i]? := by
    by_cases h : i < w <;> simp_all

theorem getElem_toListBE_eq_getMsb (x : BitVec w) (i : Nat) (h : i < x.toListBE.length) :
  x.toListBE[i] = x.getMsb ⟨i, length_toListBE x ▸ h⟩ := by
    simp [getMsb_eq_getLsb]

theorem getElem?_toListBE_eq_getMsb? (x : BitVec w) (i : Nat) :
  x.toListBE[i]? = x.getMsb? i := by
    by_cases h : i < w <;> simp [getMsb?_eq_getLsb?, h]


theorem toListBE_injective : Function.Injective (toListBE (w := w)) := by
  intro x y h
  ext i
  have : x.toListBE[w - 1 - i]'(by simp only [length_toListBE]; omega) = y.toListBE[w - 1 - i]'(by simp only [length_toListBE]; omega) := by
    simp [h]
  have weq : w - 1 - (w - 1 - i)  = i := by omega
  simpa [getElem_toListBE, weq] using this

theorem toListBE_eq_reverse_toListLE (x : BitVec w) : x.toListBE = x.toListLE.reverse := by
  apply List.ext_getElem (by simp)
  intros i h₁ h₂
  simp [getElem_toListBE, List.getElem_reverse, length_toListLE]

theorem toListLE_eq_reverse_toListBE (x : BitVec w) : x.toListLE = x.toListBE.reverse := by
  apply List.ext_getElem (by simp)
  intros i h₁ h₂
  simp only [getElem_toListLE, List.getElem_reverse, length_toListBE, getElem_toListBE]
  congr
  rw [length_toListLE] at h₁
  omega

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
      simp only [Nat.reduceSubDiff, List.getElem_cons_succ, getElem_toListBE, Nat.sub_add_eq, Nat.sub_right_comm]
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
    · rw [getElem_concat, List.getElem_append_left (by simp only [length_toListBE]; omega), dif_neg (by omega)]
      simp [Nat.sub_right_comm]
  · repeat rw [List.getElem?_eq_none (by simp only [List.length_append, length_toListBE,
    List.length_cons, List.length_nil, Nat.zero_add]; omega)]

/--
Round-trip: `ofBoolListLE` and `toList` are inverses.
-/
@[simp]
theorem toListLE_ofBoolListLE (l : List Bool) : (ofBoolListLE l).toListLE = l := by
  induction l with
  | nil => simp [ofBoolListLE, ←ofNat_eq_ofNat]
  | cons b bs ih => simp [ofBoolListLE, ih]

@[simp]
theorem toList_cast {w v : Nat} (h : w = v) (x : BitVec w) : (x.cast h).toListLE = x.toListLE := by
  subst h
  rfl

@[simp]
theorem cons_cast {w v : Nat} (h : w = v) (b : Bool) (x : BitVec w) :
  cons b (x.cast h) = (cons b x).cast (by simp [h]) := by
    subst h
    rfl

theorem ofBoolListLE_concat (l : List Bool) (b : Bool) :
  ofBoolListLE (l ++ [b]) = (cons b (ofBoolListLE l)).cast (by simp) := by
    apply toListLE_injective
    simp [toListLE_ofBoolListLE, toListLE_cons]

theorem ofBoolListLE_congr {l1 l2 : List Bool} (h : l1 = l2) :
  ofBoolListLE l1 = (ofBoolListLE l2).cast (by rw [h]) := by
    subst h
    rfl

/--
Round-trip: `toList` and `ofBoolListLE` are inverses.
-/
@[simp]
theorem ofBoolListLE_toListLE (x : BitVec w) : ofBoolListLE x.toListLE = x.cast (by simp) := by
  induction x using BitVec.induction with
  | nil => rfl
  | cons _ b x' ih =>
    calc ofBoolListLE (cons b x').toListLE
      _ = (ofBoolListLE ((toListLE x').concat b)).cast (by rw [toListLE_cons]) := by
        apply ofBoolListLE_congr
        exact toListLE_cons _ _
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
* `(0b1010#4).toArrayLE = #[false, true, false, true]`
* `(0#3).toArrayLE = #[false, false, false]`
-/
def toArrayLE (x : BitVec w) : Array Bool :=
  Array.ofFn (n := w) (fun i => x[i])

@[simp, grind =]
theorem size_toArrayLE (x : BitVec w) : x.toArrayLE.size = w := by
  simp [toArrayLE]

@[simp, grind =]
theorem getElem_toArrayLE (x : BitVec w) (i : Nat) (h : i < x.toArrayLE.size) :
  x.toArrayLE[i] = x[i]'(by simpa using h) := by
    simp [toArrayLE]

@[simp]
theorem getElem?_toArrayLE_eq_getElem? (x : BitVec w) (i : Nat) :
  x.toArrayLE[i]? = x[i]? := by
    by_cases h : i < w <;> simp [h]

theorem toArrayLE_injective : Function.Injective (toArrayLE (w := w)) := by
  intro x y h
  ext i
  have : x.toArrayLE[i]'(by simpa) = y.toArrayLE[i]'(by simpa) := by
    simp [h]
  simpa using this

@[simp]
theorem toArrayLE_inj {x y : BitVec w} : x.toArrayLE = y.toArrayLE ↔ x = y :=
  toArrayLE_injective.eq_iff

@[simp]
theorem toList_toArrayLE (x : BitVec w) : x.toArrayLE.toList = x.toListLE := by
  ext i
  by_cases h : i < w
  · simp [h, toArrayLE, toListLE]
  · repeat rw [List.getElem?_eq_none (by simp; omega)]

/--
Convert a bitvector to an array of bools (MSB first).

The resulting array has the most significant bit at index 0.

Examples:
* `(0b1010#4).toArrayBE = #[true, false, true, false]`
* `(0#3).toArrayBE = #[false, false, false]`
-/
def toArrayBE (x : BitVec w) : Array Bool :=
  Array.ofFn (n := w) (fun i => x[w - 1 - i])

@[simp, grind =]
theorem size_toArrayBE (x : BitVec w) : x.toArrayBE.size = w := by
  simp [toArrayBE]

@[simp, grind =]
theorem getElem_toArrayBE (x : BitVec w) (i : Nat) (h : i < x.toArrayBE.size) :
  x.toArrayBE[i] = x[w - 1 - i]'(by rw [size_toArrayBE] at h; omega) := by
    simp [toArrayBE]

theorem getElem_toArrayBE_eq_getMsb (x : BitVec w) (i : Nat) (h : i < x.toArrayBE.size) :
  x.toArrayBE[i] = x.getMsb ⟨i, size_toArrayBE x ▸ h⟩ := by
    simp [getMsb_eq_getLsb]

@[simp, grind =]
theorem getElem?_toArrayBE_eq_getMsb? (x : BitVec w) (i : Nat) :
  x.toArrayBE[i]? = x.getMsb? i := by
    by_cases h : i < w <;> simp [h, getMsb?_eq_getLsb?]

theorem toArrayBE_injective : Function.Injective (toArrayBE (w := w)) := by
  intros x y h
  ext i
  have : x.toArrayBE[w - 1 - i]'(by simp only [size_toArrayBE]; omega) = y.toArrayBE[w - 1 - i]'(by simp only [size_toArrayBE]; omega) := by
    simp [h]

  have weq : w - 1 - (w - 1 - i)  = i := by omega
  simpa [getElem_toArrayBE, weq] using this

@[simp]
theorem toArrayBE_inj {x y : BitVec w} : x.toArrayBE = y.toArrayBE ↔ x = y :=
  toArrayBE_injective.eq_iff

@[simp]
theorem toList_toArrayBE (x : BitVec w) : x.toArrayBE.toList = x.toListBE := by
  ext i
  by_cases h : i < w
  · simp [h, toArrayBE, toListBE]
  · repeat rw [List.getElem?_eq_none (by simp only [length_toListBE, Array.length_toList, size_toArrayBE]; omega)]

/--
Build a bitvector from an array of bools.

Takes the first `w` elements from the array. If the array is shorter than `w`,
the remaining bits are set to `false`.

Examples:
* `ofArrayLE #[false, true, false, true] = 0b1010#4`
* `ofArrayLE #[true, true] 3 = 0b011#3` (padded with false)
* `ofArrayLE #[true, true, false, true] 2 = 0b11#2` (truncated)
-/
def ofArrayLE (a : Array Bool) (w : Nat := a.size) : BitVec w :=
  ofFnLE (fun i => a.getD i.val false)

@[simp]
theorem getElem_ofArrayLE (w : Nat) (a : Array Bool) (i : Nat) (h : i < w) :
  (ofArrayLE a w)[i] = a.getD i false := by
    simp [ofArrayLE, getElem_ofFnLE]

@[simp]
theorem ofArrayLE_toArrayLE (x : BitVec w) : ofArrayLE x.toArrayLE w = x := by
  ext
  simp [ofArrayLE, getElem_ofFnLE]

@[simp]
theorem toArrayLE_ofArrayLE (a : Array Bool) : (ofArrayLE a).toArrayLE = a := by
  ext i; simp only [size_toArrayLE]
  by_cases h : i < a.size
  · simp [toArrayLE, ofArrayLE, getElem_ofFnLE]
  · contradiction

/--
Build a bitvector from an array of bools (MSB first).

Takes the first `w` elements from the array with element 0 as the most significant bit.
If the array is shorter than `w`, the remaining bits are set to `false`.

Examples:
* `ofArrayBE #[true, false, true, false] = 0b1010#4`
* `ofArrayBE #[true, true] 3 = 0b110#3` (padded with false)
* `ofArrayBE #[true, false, true, false] 2 = 0b10#2` (truncated)
-/
def ofArrayBE (a : Array Bool) (w : Nat := a.size) : BitVec w :=
  ofFnBE (fun i => a.getD i.val false)

@[simp]
theorem getElem_ofArrayBE (w : Nat) (a : Array Bool) (i : Nat) (h : i < w) :
  (ofArrayBE a w)[i] = a.getD (w - 1 - i) false := by
    simp [ofArrayBE, getElem_ofFnBE]

@[simp]
theorem ofArrayBE_toArrayBE (x : BitVec w) : ofArrayBE x.toArrayBE w = x := by
  ext
  simp only [ofArrayBE, Array.getD_eq_getD_getElem?, size_toArrayBE, Fin.is_lt, getElem?_pos,
    getElem_toArrayBE, Option.getD_some, getElem_ofFnBE]
  congr; omega

@[simp]
theorem toArrayBE_ofArrayBE (a : Array Bool) : (ofArrayBE a).toArrayBE = a := by
  ext i; simp only [size_toArrayBE]
  by_cases h : i < a.size
  · simp only [toArrayBE, ofArrayBE, Array.getD_eq_getD_getElem?, Fin.is_lt, getElem?_pos,
    Option.getD_some, getElem_ofFnBE, Array.getElem_ofFn]
    congr; omega
  · contradiction

@[simp]
theorem toArrayLE_nil : toArrayLE nil = #[] := by
  simp [toArrayLE]

@[simp]
theorem toArrayLE_concat (x : BitVec w) (b : Bool) :
  toArrayLE (concat x b) = #[b] ++ toArrayLE x := by
    apply Array.ext
    · simp only [size_toArrayLE, Array.size_append, List.size_toArray, List.length_cons,
      List.length_nil, Nat.zero_add]; omega
    · intro i h
      simp only [size_toArrayLE] at h
      simp only [getElem_toArrayLE, getElem_concat (h := h)]
      split
      · simp_all
      · have : 1 <= i := by omega
        simp_all

theorem toArray_eq_toList_toArray (x : BitVec w) : x.toArrayLE = x.toListLE.toArray := by
  ext i h₁ h₂ <;> simp

theorem toList_ofFn (f : Fin w → Bool) : (ofFnLE f).toListLE = List.ofFn f := by
  ext i
  by_cases h : i < w
  · repeat rw [List.getElem?_eq_getElem (by simpa)]
    simp [getElem_ofFnLE]
  · repeat rw [List.getElem?_eq_none (by simp; omega)]

theorem toArray_ofFn (f : Fin w → Bool) : (ofFnLE f).toArrayLE = Array.ofFn f := by
  ext <;> simp [getElem_ofFnLE]

/--
Convert a bitvector to a vector of bools (LSB first).

The resulting vector has the least significant bit at index 0.

Examples:
* `(0b1010#4).toVectorLE = #v[false, true, false, true]`
* `(0#3).toVectorLE = #v[false, false, false]`
-/
def toVectorLE (x : BitVec w) : Vector Bool w :=
  ⟨x.toArrayLE, by simp⟩

@[simp, grind =]
theorem toVector_toArray (x : BitVec w) : x.toVectorLE.toArray = x.toArrayLE := by
  simp [toVectorLE]

theorem get_toVectorLE (x : BitVec w) (i : Fin w) :
  x.toVectorLE.get i = x[i.val] := by
    simp [toVectorLE, Vector.get, toArrayLE]

theorem toVectorLE_injective : Function.Injective (toVectorLE (w := w)) := by
  intro x y h
  have : x.toArrayLE = y.toArrayLE := by
    have := congrArg Vector.toArray h
    simpa using this
  exact toArrayLE_injective this

@[simp]
theorem toVectorLE_inj {x y : BitVec w} : x.toVectorLE = y.toVectorLE ↔ x = y :=
  toVectorLE_injective.eq_iff

/--
Convert a bitvector to a vector of bools (MSB first).

The resulting vector has the most significant bit at index 0.

Examples:
* `(0b1010#4).toVectorBE = #v[true, false, true, false]`
* `(0#3).toVectorBE = #v[false, false, false]`
-/
def toVectorBE (x : BitVec w) : Vector Bool w :=
  ⟨x.toArrayBE, by simp⟩

@[simp, grind =]
theorem toVectorBE_toArray (x : BitVec w) : x.toVectorBE.toArray = x.toArrayBE := by
  simp [toVectorBE]

theorem get_toVectorBE (x : BitVec w) (i : Fin w) :
  x.toVectorBE.get i = x[w - 1 - i.val] := by
    simp [toVectorBE, Vector.get, toArrayBE]

theorem get_toVectorBE_eq_getMsb (x : BitVec w) (i : Fin w) :
  x.toVectorBE.get i = x.getMsb i := by
    simp [getMsb, get_toVectorBE]

theorem toVectorBE_injective : Function.Injective (toVectorBE (w := w)) := by
  intro x y h
  have : x.toArrayBE = y.toArrayBE := by
    have := congrArg Vector.toArray h
    simpa using this
  exact toArrayBE_injective this

@[simp]
theorem toVectorBE_inj {x y : BitVec w} : x.toVectorBE = y.toVectorBE ↔ x = y :=
  toVectorBE_injective.eq_iff

/--
Build a bitvector from a vector of bools.

The vector must have exactly `w` elements.

Examples:
* `ofVectorLE #v[false, true, false, true] = 0b1010#4`
* `ofVectorLE #v[true, true, true] = 0b111#3`
-/
def ofVectorLE (v : Vector Bool w) : BitVec w :=
  ofArrayLE v.toArray w

@[simp]
theorem getElem_ofVectorLE (v : Vector Bool w) (i : Nat) (h : i < w) :
  (ofVectorLE v)[i] = v.get ⟨i, h⟩ := by
    simp [ofVectorLE, ofArrayLE, getElem_ofFnLE, Vector.get]

@[simp]
theorem ofVectorLE_toVectorLE (x : BitVec w) : ofVectorLE x.toVectorLE = x := by
  simp [ofVectorLE, toVectorLE]

@[simp]
theorem toVectorLE_ofVectorLE (v : Vector Bool w) : (ofVectorLE v).toVectorLE = v := by
  rcases v with ⟨arr, rfl⟩
  simp [toVectorLE, ofVectorLE]

/--
Build a bitvector from a vector of bools (MSB first).

The vector must have exactly `w` elements, with element 0 as the most significant bit.

Examples:
* `ofVectorBE #v[true, false, true, false] = 0b1010#4`
* `ofVectorBE #v[true, true, true] = 0b111#3`
-/
def ofVectorBE (v : Vector Bool w) : BitVec w :=
  ofArrayBE v.toArray w

@[simp]
theorem getElem_ofVectorBE (v : Vector Bool w) (i : Nat) (h : i < w) :
  (ofVectorBE v)[i] = v.get ⟨w - 1 - i, by omega⟩ := by
    simp [ofVectorBE, ofArrayBE, getElem_ofFnBE, Vector.get]

@[simp]
theorem ofVectorBE_toVectorBE (x : BitVec w) : ofVectorBE x.toVectorBE = x := by
  simp [ofVectorBE, toVectorBE]

@[simp]
theorem toVectorBE_ofVectorBE (v : Vector Bool w) : (ofVectorBE v).toVectorBE = v := by
  rcases v with ⟨arr, rfl⟩
  simp [toVectorBE, ofVectorBE]

@[simp]
theorem toVectorLE_nil : toVectorLE nil = #v[] := by
  ext
  contradiction

@[simp]
theorem toVector_concat (x : BitVec w) (b : Bool) :
  toVectorLE (concat x b) = Vector.mk (#[b] ++ x.toArrayLE) (by simp +arith) := by
    apply Vector.ext
    simp [toVectorLE, Vector.getElem_mk]

theorem toList_toVectorLE (x : BitVec w) : x.toVectorLE.toList = x.toListLE := by
  simp [Vector.toList, toVectorLE]

/-! ## ByteArray conversions

Converting between `BitVec` and `ByteArray` handles byte alignment automatically.

**Round-trip behavior (applies to both LE and BE):**
* `toBytes{LE,BE}` pads the width up to the next byte boundary: `w → (w + 7) / 8 * 8`
* `ofBytes{LE,BE} (x.toBytes{LE,BE})` returns a `BitVec` with width `(w + 7) / 8 * 8`
* Perfect round-trip: `(ofBytes{LE,BE} bytes).toBytes{LE,BE} = bytes`
* Width changes: `ofBytes{LE,BE} x.toBytes{LE,BE} = x.zeroExtend ((w + 7) / 8 * 8)`

**Example of width change:**
* `x : BitVec 9` has width 9, but `x.toBytesLE` has size 2 (requires 2 bytes)
* `ofBytesLE x.toBytesLE` returns `BitVec 16` (not `BitVec 9`)
* When `w % 8 = 0`, the width is preserved (see `ofBytesLE_toBytesLE_of_aligned`)

**Padding direction:**
* LE: Zero-padding goes in high bits of the *last* byte
* BE: Zero-padding goes in high bits of the *first* byte
-/

/--
Convert a bitvector to a byte array (little-endian).

The byte at index 0 contains bits 0-7 (the least significant byte).
If the width is not a multiple of 8, the most significant bits of the last byte are zero-padded.

Examples:
* `(0x1234#16).toBytesLE.data = #[0x34, 0x12]`
* `(0xAB#8).toBytesLE.data = #[0xAB]`
* `(0b101#3).toBytesLE.data = #[0b00000101]`
-/
def toBytesLE (x : BitVec w) : ByteArray :=
  let numBytes := (w + 7) / 8
  ByteArray.mk <| Array.ofFn fun (i : Fin numBytes) =>
    UInt8.ofBitVec (x.extractLsb' (i.val * 8) 8)

@[simp]
theorem size_toBytesLE (x : BitVec w) : x.toBytesLE.size = (w + 7) / 8 := by
  simp [toBytesLE, ByteArray.size]

@[simp]
theorem getElem_toBytesLE (x : BitVec w) (i : Nat) (h : i < (w + 7) / 8) :
  x.toBytesLE[i]'(size_toBytesLE _ ▸ h) =
  UInt8.ofBitVec (x.extractLsb' (i * 8) 8) := by
    simp [toBytesLE, ByteArray.getElem_eq_getElem_data]

private theorem getLsbD_toBytesLE {w : Nat} (x : BitVec w) (i : Nat) (h : i < x.toBytesLE.size * 8) :
  (x.toBytesLE)[i / 8].toBitVec.getLsbD (i % 8) = x.getLsbD i := by
    unfold toBytesLE
    simp only [ByteArray.getElem_eq_getElem_data]
    rw [Array.getElem_ofFn]
    simp only [getLsbD_extractLsb',
              Nat.mod_lt _ (y := 8) (by decide)]
    simp [Nat.mul_comm, Nat.div_add_mod i 8]


@[simp]
theorem toBytesLE_cast {w v : Nat} (h : w = v) (x : BitVec w) : (x.cast h).toBytesLE = x.toBytesLE := by
  subst h
  rfl

/--
Convert a bitvector to a byte array (big-endian).

The byte at index 0 contains the most significant 8 bits.
If the width is not a multiple of 8, the most significant bits of the first byte are zero-padded.

Examples:
* `(0x1234#16).toBytesBE.data = #[0x12, 0x34]`
* `(0xAB#8).toBytesBE.data = #[0xAB]`
* `(0b101#3).toBytesBE.data = #[0b00000101]`
-/
def toBytesBE (x : BitVec w) : ByteArray :=
  ⟨x.toBytesLE.data.reverse⟩

@[simp]
theorem size_toBytesBE (x : BitVec w) : x.toBytesBE.size = (w + 7) / 8 := by
  unfold toBytesBE
  rw [←ByteArray.size_data]
  simp

@[simp]
theorem getElem_toBytesBE (x : BitVec w) (i : Nat) (h : i < (w + 7) / 8) :
  x.toBytesBE[i]'(size_toBytesBE _ ▸ h) =
  UInt8.ofBitVec (x.extractLsb' (((w + 7) / 8 - 1 - i) * 8) 8) := by
    unfold toBytesBE toBytesLE
    simp [ByteArray.getElem_eq_getElem_data, Array.getElem_ofFn]

@[simp]
theorem toBytesBE_cast {w v : Nat} (h : w = v) (x : BitVec w) : (x.cast h).toBytesBE = x.toBytesBE := by
  subst h
  rfl

/--
Build a bitvector from a byte array (little-endian).

The byte at index 0 becomes bits 0-7 (the least significant byte).

Examples:
* `ofBytesLE (ByteArray.mk #[0x34, 0x12]) = 0x1234#16`
* `ofBytesLE (ByteArray.mk #[0xAB]) = 0xAB#8`
* `ofBytesLE (ByteArray.mk #[0xFF, 0x0F]) = 0xFFF#16`
-/
def ofBytesLE (bytes : ByteArray) : BitVec (bytes.size * 8) :=
  (Array.range bytes.size).foldl (init := 0) fun r i =>
    r ||| ((BitVec.zeroExtend _ bytes[i]!.toBitVec) <<< (i * 8))

private theorem Array.foldl_singleton (α β : Type u) (a : α) (init : β) (f : β → α → β) :
  Array.foldl f init #[a] = f init a := by
    simp [Array.foldl]

private theorem getLsbD_ofBytesLE_aux (bytes : ByteArray) (k : Nat) (hk : k ≤ bytes.size) :
    ∀ j, ((Array.range k).foldl (fun r i => r ||| ((BitVec.zeroExtend (bytes.size * 8) bytes[i]!.toBitVec) <<< (i * 8))) 0).getLsbD j =
      (if j / 8 < k then bytes[j / 8]!.toBitVec.getLsbD (j % 8) else false) := by
  induction k with
  | zero =>
    simp [Array.range_eq_empty_iff.mpr rfl, BitVec.getLsbD_zero]
  | succ k ih =>
    intro j
    rw [Array.range_succ, Array.foldl_append, Array.foldl_singleton,
        BitVec.getLsbD_or, ih (Nat.le_of_succ_le hk) j,
        BitVec.getLsbD_shiftLeft]
    split
    · simp [Nat.lt_succ_of_lt ‹_›, (by omega : j < k * 8)]
    · split
      · simp only [show k = j / 8 by omega,
                   show ¬ j < j / 8 * 8 by omega]
        rw [← Nat.mod_eq_sub_div_mul]
        simp_all [show j < bytes.size * 8 by omega,
                  show j % 8 < bytes.size * 8 by omega]
      · rw [zeroExtend_eq_setWidth, getLsbD_setWidth]
        simp only [Bool.false_or, show ¬ (j < k * 8) by omega]
        rw [getLsbD_of_ge]
        · simp
        · omega

@[simp]
theorem getElem_ofBytesLE (bytes : ByteArray) (j : Nat) (h : j < bytes.size * 8) :
  (ofBytesLE bytes)[j] = bytes[j / 8].toBitVec[j % 8] := by
    unfold ofBytesLE
    rw [← getLsbD_eq_getElem h,
        getLsbD_ofBytesLE_aux _ _ (Nat.le_refl _)]
    rw [Nat.mul_comm] at h
    rw [if_pos (Nat.div_lt_of_lt_mul h), getLsbD_eq_getElem,
        getElem!_pos bytes _ (Nat.div_lt_of_lt_mul h)]

/--
Build a bitvector from a byte array (big-endian).

The byte at index 0 becomes the most significant 8 bits.

Examples:
* `ofBytesBE (ByteArray.mk #[0x12, 0x34]) = 0x1234#16`
* `ofBytesBE (ByteArray.mk #[0xAB]) = 0xAB#8`
* `ofBytesBE (ByteArray.mk #[0x0F, 0xFF]) = 0xFFF#16`
-/
def ofBytesBE (bytes : ByteArray) : BitVec (bytes.size * 8) :=
  (ofBytesLE ⟨bytes.data.reverse⟩).cast (by simp [←ByteArray.size_data])

@[simp]
theorem getElem_ofBytesBE (bytes : ByteArray) (j : Nat) (h : j < bytes.size * 8) :
  (ofBytesBE bytes)[j] = bytes[bytes.size - 1 - j / 8].toBitVec[j % 8] := by
  simp [ofBytesBE, getElem_ofBytesLE, ByteArray.getElem_eq_getElem_data]

@[simp]
theorem toBytesLE_ofBytesLE (bytes : ByteArray) :
    (ofBytesLE bytes).toBytesLE = bytes := by
  ext i hi hi'
  · simp only [ByteArray.size_data, size_toBytesLE]
    rw [Nat.mul_comm, Nat.mul_add_div (m := 8) (by decide)]
    simp
  · unfold toBytesLE
    rw [Array.getElem_ofFn]
    congr
    ext j hj
    have : i * 8 + j < bytes.size * 8 := by
      rw [←ByteArray.size_data]
      omega
    simp [getLsbD_eq_getElem this, getElem_ofBytesLE,
          Nat.mod_eq_of_lt hj,
          show (i * 8 + j) / 8 = i by omega,
          ByteArray.getElem_eq_getElem_data]

@[simp]
theorem ofBytesLE_toBytesLE (x : BitVec w) :
  ofBytesLE x.toBytesLE = x.zeroExtend (x.toBytesLE.size * 8) := by
    ext i hi
    rw [getElem_ofBytesLE _ _ hi, ←getLsbD_eq_getElem,
        getLsbD_toBytesLE _ _ hi]
    simp only [zeroExtend]
    rw [getElem_setWidth]

theorem ofBytesLE_toBytesLE_of_aligned (x : BitVec w) (h : w % 8 = 0) :
  ofBytesLE x.toBytesLE = x.cast (by rw [size_toBytesLE]; omega) := by
    rw [ofBytesLE_toBytesLE]
    ext i h
    simp only [truncate_eq_setWidth, getElem_setWidth, getElem_cast]
    rw [getLsbD_eq_getElem (by rw [size_toBytesLE] at h; omega)]


@[simp]
theorem toBytesBE_ofBytesBE (bytes : ByteArray) :
    (ofBytesBE bytes).toBytesBE = bytes := by
  unfold ofBytesBE toBytesBE
  simp only [toBytesLE_cast, toBytesLE_ofBytesLE]
  exact ByteArray.mk.injEq _ _ |>.mpr (Array.reverse_reverse _)

@[simp]
theorem ofBytesBE_toBytesBE (x : BitVec w) :
    ofBytesBE x.toBytesBE = x.zeroExtend (x.toBytesBE.size * 8) := by
  ext i hi
  rw [getElem_ofBytesBE _ _ hi, getElem_toBytesBE]
  · simp only [size_toBytesBE, getElem_extractLsb', truncate_eq_setWidth, getElem_setWidth] at hi ⊢
    rw [Nat.sub_sub_self]
    · congr
      rw [Nat.mul_comm, Nat.div_add_mod]
    · omega
  · simp only [size_toBytesBE] at hi ⊢
    omega

theorem ofBytesBE_toBytesBE_of_aligned (x : BitVec w) (h : w % 8 = 0) :
  ofBytesBE x.toBytesBE = x.cast (by rw [size_toBytesBE]; omega) := by
    rw [ofBytesBE_toBytesBE]
    ext i h
    simp only [truncate_eq_setWidth, getElem_setWidth, getElem_cast]
    rw [getLsbD_eq_getElem (by rw [size_toBytesBE] at h; omega)]

/-! ### Injectivity -/

theorem toBytesLE_injective : Function.Injective (toBytesLE (w := w)) := by
  intro x y h
  ext i hi
  have : (x.toBytesLE[i / 8]'(by simp; omega)).toBitVec.getLsbD (i % 8) =
         (y.toBytesLE[i / 8]'(by simp; omega)).toBitVec.getLsbD (i % 8) := by
    simp [h]
  rw [getLsbD_toBytesLE, getLsbD_toBytesLE] at this
  · repeat rw [getLsbD_eq_getElem hi] at this
    exact this
  · simp only [size_toBytesLE]; omega
  · simp only [size_toBytesLE]; omega

@[simp]
theorem toBytesLE_inj {x y : BitVec w} : x.toBytesLE = y.toBytesLE ↔ x = y :=
  toBytesLE_injective.eq_iff

theorem toBytesBE_injective : Function.Injective (toBytesBE (w := w)) := by
  intro x y h
  have : x.toBytesLE = y.toBytesLE := by
    unfold toBytesBE at h
    have := congrArg ByteArray.data h
    exact ByteArray.ext (Array.reverse_inj.mp this)
  exact toBytesLE_injective this

@[simp]
theorem toBytesBE_inj {x y : BitVec w} : x.toBytesBE = y.toBytesBE ↔ x = y :=
  toBytesBE_injective.eq_iff

/-! ### Basic cases -/

@[simp]
theorem toBytesLE_zero : (0 : BitVec w).toBytesLE =
    ByteArray.mk (Array.replicate ((w + 7) / 8) 0) := by
  ext i hi hi'
  · simp [size_toBytesLE]
  · rw [Array.getElem_replicate, ←ByteArray.getElem_eq_getElem_data,
        getElem_toBytesLE (h := by simp_all)]
    simp

@[simp]
theorem toBytesBE_zero : (0 : BitVec w).toBytesBE =
    ByteArray.mk (Array.replicate ((w + 7) / 8) 0) := by
  unfold toBytesBE
  rw [toBytesLE_zero]
  simp [Array.reverse_replicate]

@[simp]
theorem ofBytesLE_empty : ofBytesLE ByteArray.empty = 0#0 := by
  unfold ofBytesLE
  simp [←ByteArray.size_data,
        Array.range_eq_empty_iff.mpr rfl, Array.size_empty]

@[simp]
theorem ofBytesBE_empty : ofBytesBE ByteArray.empty = 0#0 := by
  unfold ofBytesBE
  simp [ofBytesLE, ←ByteArray.size_data,
        Array.range_eq_empty_iff.mpr rfl, Array.size_empty]
  

/-! ### LE/BE relationships -/

theorem toBytesBE_eq_reverse_toBytesLE (x : BitVec w) :
  x.toBytesBE = ⟨x.toBytesLE.data.reverse⟩ := by simp [toBytesBE]

theorem toBytesLE_eq_reverse_toBytesBE (x : BitVec w) :
  x.toBytesLE = ⟨x.toBytesBE.data.reverse⟩ := by
    unfold toBytesBE
    simp [Array.reverse_reverse]

theorem ofBytesBE_eq_cast_ofBytesLE_reverse (bytes : ByteArray) :
  ofBytesBE bytes = (ofBytesLE ⟨bytes.data.reverse⟩).cast (by simp [←ByteArray.size_data]) := by simp [ofBytesBE]

theorem ofBytesLE_eq_cast_ofBytesBE_reverse (bytes : ByteArray) :
  ofBytesLE bytes = (ofBytesBE ⟨bytes.data.reverse⟩).cast (by simp [←ByteArray.size_data]) := by
    unfold ofBytesBE
    dsimp
    ext i hi
    simp
  

end BitVec
