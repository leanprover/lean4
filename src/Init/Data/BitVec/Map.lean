/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fady Adal
-/
module

prelude
public import Init.Data.BitVec.OfFn

public section

set_option linter.missingDocs true

namespace BitVec

/-!
## Transformation operations

This module provides operations for transforming bitvectors through mapping
and zipping operations.
-/

/--
Map a function over all bits.

Applies the function `f` to each bit in the bitvector, producing a new bitvector.

Examples:
* `(0b1010#4).map not = 0b0101#4`
* `(0b1111#4).map id = 0b1111#4`
* `nil.map f = nil`
-/
def map (x : BitVec w) (f : Bool → Bool) : BitVec w :=
  ofFn (fun i => f x[i])

@[simp]
theorem map_nil (f : Bool → Bool) : map nil f = nil := by
  simp [map, -ofNat_eq_ofNat]

@[simp]
theorem getElem_map (x : BitVec w) (f : Bool → Bool) (i : Nat) (h : i < w) :
    (x.map f)[i] = f x[i] := by
  simp [map, getElem_ofFn]

theorem getLsbD_map (x : BitVec w) (f : Bool → Bool) (i : Nat) :
    (x.map f).getLsbD i = if h : i < w then f x[i] else false := by
  by_cases h : i < w
  · simp [h, getElem_map]
  · simp only [h, ↓reduceDIte]
    apply getLsbD_of_ge
    omega

@[simp]
theorem map_cons (f : Bool → Bool) (b : Bool) (x : BitVec w) :
    map (cons b x) f = cons (f b) (map x f) := by
  ext i
  simp [getElem_cons]
  split <;> simp

theorem map_map (x : BitVec w) (f g : Bool → Bool) :
    (x.map f).map g = x.map (g ∘ f) := by
  ext i
  simp

@[simp]
theorem map_id (x : BitVec w) : x.map id = x := by
  ext i
  simp

/--
Map with index.

Applies the function `f` to each bit along with its index (from LSB to MSB).

Examples:
* `(0b1010#4).mapIdx (fun i b => i.val % 2 == 0 && b) = 0b1000#4`
* `nil.mapIdx f = nil`
-/
def mapIdx (x : BitVec w) (f : Fin w → Bool → Bool) : BitVec w :=
  ofFn (fun i => f i x[i])

@[simp]
theorem mapIdx_nil (f : Fin 0 → Bool → Bool) : mapIdx nil f = nil := by
  simp [mapIdx, -ofNat_eq_ofNat]

@[simp]
theorem getElem_mapIdx (x : BitVec w) (f : Fin w → Bool → Bool) (i : Nat) (h : i < w) :
    (x.mapIdx f)[i] = f ⟨i, h⟩ x[i] := by
  simp [mapIdx, getElem_ofFn]

theorem getLsbD_mapIdx (x : BitVec w) (f : Fin w → Bool → Bool) (i : Nat) :
    (x.mapIdx f).getLsbD i = if h : i < w then f ⟨i, h⟩ x[i] else false := by
  by_cases h : i < w
  · simp [h, getElem_mapIdx]
  · simp only [h, ↓reduceDIte]
    apply getLsbD_of_ge
    omega

theorem mapIdx_eq_map_of_independent (x : BitVec w) (f : Fin w → Bool → Bool) (g : Bool → Bool)
    (h : ∀ i b, f i b = g b) :
    x.mapIdx f = x.map g := by
  ext i
  simp [h]

/--
Zip two bitvectors with a function.

Combines corresponding bits from two bitvectors using function `f`.

Examples:
* `(0b1100#4).zipWith (fun a b => a && b) (0b1010#4) = 0b1000#4`
* `(0b1100#4).zipWith (fun a b => a || b) (0b1010#4) = 0b1110#4`
* `x.zipWith (fun a b => a ^^ b) y = x ^^^ y`
-/
def zipWith (f : Bool → Bool → Bool) (x y : BitVec w) : BitVec w :=
  ofFn (fun i => f x[i] y[i])

@[simp]
theorem zipWith_nil (f : Bool → Bool → Bool) : zipWith f nil nil = nil := by
  simp [zipWith, -ofNat_eq_ofNat]

@[simp]
theorem getElem_zipWith (f : Bool → Bool → Bool) (x y : BitVec w) (i : Nat) (h : i < w) :
    (zipWith f x y)[i] = f x[i] y[i] := by
  simp [zipWith, getElem_ofFn]

theorem getLsbD_zipWith (f : Bool → Bool → Bool) (x y : BitVec w) (i : Nat) :
    (zipWith f x y).getLsbD i = if h : i < w then f x[i] y[i] else false := by
  by_cases h : i < w
  · simp [h, getElem_zipWith]
  · simp only [h, ↓reduceDIte]
    apply getLsbD_of_ge
    omega

@[simp]
theorem zipWith_cons (f : Bool → Bool → Bool) (a b : Bool) (x y : BitVec w) :
    zipWith f (cons a x) (cons b y) = cons (f a b) (zipWith f x y) := by
  ext
  simp only [getElem_zipWith, getElem_cons]
  split <;> simp

theorem and_eq_zipWith (x y : BitVec w) : x &&& y = zipWith (· && ·) x y := by
  ext
  simp [getElem_and]

theorem or_eq_zipWith (x y : BitVec w) : x ||| y = zipWith (· || ·) x y := by
  ext
  simp [getElem_or]

theorem xor_eq_zipWith (x y : BitVec w) : x ^^^ y = zipWith xor x y := by
  ext
  simp [getElem_xor]
  

theorem complement_eq_map (x : BitVec w) : ~~~x = x.map not := by
  ext
  simp [getElem_not]

theorem zipWith_comm (f : Bool → Bool → Bool) (hf : ∀ a b, f a b = f b a)
    (x y : BitVec w) :
    zipWith f x y = zipWith f y x := by
  ext
  simp [hf]

theorem zipWith_assoc (f : Bool → Bool → Bool)
    (hf : ∀ a b c, f (f a b) c = f a (f b c))
    (x y z : BitVec w) :
    zipWith f (zipWith f x y) z = zipWith f x (zipWith f y z) := by
  ext
  simp [hf]

theorem map_eq_iff {x : BitVec w} {f g : Bool → Bool} :
    x.map f = x.map g ↔ ∀ (i : Nat) (h : i < w), f x[i] = g x[i] := by
  constructor
  · intro heq i h
    have : (x.map f)[i] = (x.map g)[i] := by rw [heq]
    simpa using this
  · intro h
    ext i
    simp [h]

theorem zipWith_self (f : Bool → Bool → Bool) (x : BitVec w) :
    zipWith f x x = x.map (fun a => f a a) := by
  ext
  simp

theorem zipWith_map_left (f : Bool → Bool → Bool) (g : Bool → Bool) (x y : BitVec w) :
    zipWith f (x.map g) y = zipWith (fun a b => f (g a) b) x y := by
  ext
  simp

theorem zipWith_map_right (f : Bool → Bool → Bool) (g : Bool → Bool) (x y : BitVec w) :
    zipWith f x (y.map g) = zipWith (fun a b => f a (g b)) x y := by
  ext
  simp

theorem map_zipWith (f : Bool → Bool) (g : Bool → Bool → Bool) (x y : BitVec w) :
    (zipWith g x y).map f = zipWith (fun a b => f (g a b)) x y := by
  ext
  simp

theorem mapIdx_congr (f g : Fin w → Bool → Bool) (h : ∀ i b, f i b = g i b) (x : BitVec w) :
    x.mapIdx f = x.mapIdx g := by
  ext i
  simp [h]

end BitVec
