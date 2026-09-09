/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.Internal.ForIn.Basic
public import Init.Data.List.Control
public import Init.Data.Array.Basic
public import Init.Data.Range.Basic
public import Init.Data.Range.Polymorphic.Lemmas
public import Init.Data.Iterators.Lemmas.Consumers.Loop
public import Init.Data.Slice.Lemmas
public import Init.Data.Iterators.Lemmas.Consumers.Monadic.Loop
import Init.Data.Array.Bootstrap
import Init.Data.Array.Lemmas
import Init.Data.List.Basic
import Init.Data.List.Monadic
import Init.Data.List.Range
import Init.Data.Nat.Dvd
import Init.Data.Range.Lemmas
import Init.Omega

/-!
# `ForIn.toList` of the effect-free containers

Each bridge lemma computes `ForIn.toList` for one container, in the spelling that carries the
membership lemmas the verification conditions need, and each instance records that the container's
loop is effect-free.
-/

@[expose] public section

namespace Std.Internal

universe u u₁ v w

private theorem forIn'_cast {γ : Type u₁} {δ : Type u} {n : Type u → Type v} [Monad n]
    {l l' : List γ} (hl : l = l') (init : δ) (f : (a : γ) → a ∈ l' → δ → n (ForInStep δ)) :
    forIn' l init (fun a ha b => f a (hl ▸ ha) b) = forIn' l' init f :=
  List.forIn'_congr hl rfl fun _ _ _ => rfl

section List

@[simp, grind =] theorem ForIn.toList_list {γ : Type u₁} (xs : List γ) : ForIn.toList xs = xs := by
  simp only [ForIn.toList, ForIn.toArray, Id.run, List.forIn_pure_yield_eq_foldl]
  change (List.foldl (fun acc a => acc.push a) #[] xs).toList = xs
  rw [foldl_push_toList]; simp

instance {α : Type u₁} : LawfulMemForInId (List α) α where
  mem_toList_iff {_a _xs} := by rw [ForIn.toList_list]

instance {m : Type u → Type v} [Monad m] {α : Type u₁} : PureForIn' m (List α) α where
  forIn'_eq xs init f := (forIn'_cast (ForIn.toList_list xs) init f).symm

instance {m : Type u → Type v} [Monad m] {α : Type u₁} : PureForIn m (List α) α where
  forIn_eq xs init f := by rw [ForIn.toList_list]

end List

section Array

@[simp, grind =] theorem ForIn.toList_array {γ : Type u₁} (xs : Array γ) :
    ForIn.toList xs = xs.toList := by
  simp only [ForIn.toList, ForIn.toArray, Id.run, ← Array.forIn_toList,
    List.forIn_pure_yield_eq_foldl]
  change (List.foldl (fun acc a => acc.push a) #[] xs.toList).toList = xs.toList
  rw [foldl_push_toList]; simp

instance {α : Type u₁} : LawfulMemForInId (Array α) α where
  mem_toList_iff {_a _xs} := by rw [ForIn.toList_array]; exact Array.mem_toList_iff

instance {m : Type u → Type v} [Monad m] {α : Type u₁} : PureForIn' m (Array α) α where
  forIn'_eq xs init f :=
    ((forIn'_cast (ForIn.toList_array xs) init
      (fun a ha b => f a (Array.mem_toList_iff.mp ha) b)).trans Array.forIn'_toList).symm

instance {m : Type u → Type v} [Monad m] {α : Type u₁} : PureForIn m (Array α) α where
  forIn_eq xs init f := by rw [ForIn.toList_array, Array.forIn_toList]

end Array

section LegacyRange

@[simp, grind =] theorem ForIn.toList_range (r : Std.Legacy.Range) :
    ForIn.toList r = List.range' r.start r.size r.step := by
  simp only [ForIn.toList, ForIn.toArray, Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl]
  change (List.foldl (fun acc a => acc.push a) #[]
    (List.range' r.start r.size r.step)).toList = _
  rw [foldl_push_toList]; simp

instance : LawfulMemForInId Std.Legacy.Range Nat where
  mem_toList_iff {a r} := by
    rw [ForIn.toList_range]
    refine ⟨Std.Legacy.Range.mem_of_mem_range', fun h => ?_⟩
    obtain ⟨hlo, hhi, hmod⟩ := h
    have hs := r.step_pos
    have hdvd : (a - r.start) / r.step * r.step = a - r.start :=
      Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmod)
    rw [List.mem_range']
    refine ⟨(a - r.start) / r.step, ?_, ?_⟩
    · simp only [Std.Legacy.Range.size]
      rw [Nat.div_lt_iff_lt_mul hs]
      have hceil : r.stop - r.start ≤ (r.stop - r.start + r.step - 1) / r.step * r.step := by
        have hdm := Nat.div_add_mod (r.stop - r.start + r.step - 1) r.step
        have hml := Nat.mod_lt (r.stop - r.start + r.step - 1) hs
        rw [Nat.mul_comm] at hdm
        omega
      omega
    · rw [Nat.mul_comm, hdvd]; omega

instance {m : Type u → Type v} [Monad m] : PureForIn' m Std.Legacy.Range Nat where
  forIn'_eq r init f := by
    rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
    exact (forIn'_cast (ForIn.toList_range r) init
      (fun a ha b => f a (Std.Legacy.Range.mem_of_mem_range' ha) b)).symm

instance {m : Type u → Type v} [Monad m] : PureForIn m Std.Legacy.Range Nat where
  forIn_eq r init f := by
    rw [ForIn.toList_range]; exact Std.Legacy.Range.forIn_eq_forIn_range' ..

end LegacyRange

section Iter

open Std.Iterators in
/-- `ForIn.toList` on an iterator is the iterator's own `toList`, so every container whose `ForIn`
loop iterates its `Std.ToIterator` reaches the iterator lemmas through this one step. -/
@[simp, grind =] theorem ForIn.toList_iter {α γ : Type w} [Iterator α Id γ]
    [Finite α Id] [IteratorLoop α Id Id] [LawfulIteratorLoop α Id Id] (it : Iter (α := α) γ) :
    ForIn.toList it = it.toList := by
  simp only [ForIn.toList, ForIn.toArray, Id.run, ← Iter.forIn_toList,
    List.forIn_pure_yield_eq_foldl]
  change (List.foldl (fun acc a => acc.push a) #[] it.toList).toList = it.toList
  rw [foldl_push_toList]; simp

open Std.Iterators in
instance {α γ : Type w} {m : Type w → Type v} [Monad m] [LawfulMonad m]
    [Iterator α Id γ] [Finite α Id] [IteratorLoop α Id m] [LawfulIteratorLoop α Id m]
    [IteratorLoop α Id Id] [LawfulIteratorLoop α Id Id] :
    PureForIn m (Iter (α := α) γ) γ where
  forIn_eq it init f := by rw [ForIn.toList_iter]; exact Iter.forIn_toList.symm

end Iter

section IterM

open Std.Iterators in
/-- `ForIn.toList` on a pure monadic iterator is the iterator's own `toList`. -/
@[simp, grind =] theorem ForIn.toList_iterM_id {α γ : Type w} [Iterator α Id γ] [Finite α Id]
    [IteratorLoop α Id Id] [LawfulIteratorLoop α Id Id] (it : IterM (α := α) Id γ) :
    ForIn.toList it = it.toList.run := by
  simp only [ForIn.toList, ForIn.toArray, Id.run, ← IterM.forIn_toList,
    List.forIn_pure_yield_eq_foldl]
  change (List.foldl (fun acc a => acc.push a) #[] it.toList.run).toList = it.toList.run
  rw [foldl_push_toList]; simp

open Std.Iterators in
instance {α γ : Type w} {m : Type w → Type v} [Monad m] [LawfulMonad m]
    [Iterator α Id γ] [Finite α Id] [IteratorLoop α Id m] [LawfulIteratorLoop α Id m]
    [IteratorLoop α Id Id] [LawfulIteratorLoop α Id Id] :
    PureForIn m (IterM (α := α) Id γ) γ where
  forIn_eq it init f := by rw [ForIn.toList_iterM_id]; exact IterM.forIn_toList.symm

end IterM

section PRange
open Std.PRange

section Rcc
variable {α : Type u} [LE α] [DecidableLE α] [UpwardEnumerable α] [Rxc.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]

theorem ForIn.toList_rcc (r : Rcc α) : ForIn.toList r = r.toList := by
  simp only [ForIn.toList, ForIn.toArray, Id.run, forIn, Rcc.forIn'_eq_forIn'_toList,
    List.forIn'_pure_yield_eq_foldl]
  change (List.foldl (fun acc a => acc.push a.val) #[] r.toList.attach).toList = r.toList
  rw [← List.foldl_map (f := Subtype.val) (g := fun acc a => Array.push acc a),
    List.attach_map_subtype_val, foldl_push_toList]
  simp

instance : LawfulMemForInId (Rcc α) α where
  mem_toList_iff {_a _r} := by rw [ForIn.toList_rcc]; exact Rcc.mem_toList_iff_mem

instance {m : Type u → Type v} [Monad m] [LawfulMonad m] : PureForIn' m (Rcc α) α where
  forIn'_eq r init f :=
    ((forIn'_cast (ForIn.toList_rcc r) init
      (fun a ha b => f a (Rcc.mem_toList_iff_mem.mp ha) b)).trans
        Rcc.forIn'_toList_eq_forIn').symm

instance {m : Type u → Type v} [Monad m] [LawfulMonad m] : PureForIn m (Rcc α) α where
  forIn_eq r init f := by
    show forIn' r init (fun a _ b => f a b) = _
    rw [PureForIn'.forIn'_eq (m := m)]
    exact forIn'_eq_forIn _ _ _ _ (fun _ _ _ => rfl)

end Rcc

section Rco
variable {α : Type u} [LE α] [LT α] [DecidableLT α] [UpwardEnumerable α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α]

theorem ForIn.toList_rco (r : Rco α) : ForIn.toList r = r.toList := by
  simp only [ForIn.toList, ForIn.toArray, Id.run, forIn, Rco.forIn'_eq_forIn'_toList,
    List.forIn'_pure_yield_eq_foldl]
  change (List.foldl (fun acc a => acc.push a.val) #[] r.toList.attach).toList = r.toList
  rw [← List.foldl_map (f := Subtype.val) (g := fun acc a => Array.push acc a),
    List.attach_map_subtype_val, foldl_push_toList]
  simp

instance : LawfulMemForInId (Rco α) α where
  mem_toList_iff {_a _r} := by rw [ForIn.toList_rco]; exact Rco.mem_toList_iff_mem

instance {m : Type u → Type v} [Monad m] [LawfulMonad m] : PureForIn' m (Rco α) α where
  forIn'_eq r init f :=
    ((forIn'_cast (ForIn.toList_rco r) init
      (fun a ha b => f a (Rco.mem_toList_iff_mem.mp ha) b)).trans
        Rco.forIn'_toList_eq_forIn').symm

instance {m : Type u → Type v} [Monad m] [LawfulMonad m] : PureForIn m (Rco α) α where
  forIn_eq r init f := by
    show forIn' r init (fun a _ b => f a b) = _
    rw [PureForIn'.forIn'_eq (m := m)]
    exact forIn'_eq_forIn _ _ _ _ (fun _ _ _ => rfl)

end Rco

section Rci
variable {α : Type u} [LE α] [UpwardEnumerable α] [Rxi.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]

theorem ForIn.toList_rci (r : Rci α) : ForIn.toList r = r.toList := by
  simp only [ForIn.toList, ForIn.toArray, Id.run, forIn, Rci.forIn'_eq_forIn'_toList,
    List.forIn'_pure_yield_eq_foldl]
  change (List.foldl (fun acc a => acc.push a.val) #[] r.toList.attach).toList = r.toList
  rw [← List.foldl_map (f := Subtype.val) (g := fun acc a => Array.push acc a),
    List.attach_map_subtype_val, foldl_push_toList]
  simp

instance : LawfulMemForInId (Rci α) α where
  mem_toList_iff {_a _r} := by rw [ForIn.toList_rci]; exact Rci.mem_toList_iff_mem

instance {m : Type u → Type v} [Monad m] [LawfulMonad m] : PureForIn' m (Rci α) α where
  forIn'_eq r init f :=
    ((forIn'_cast (ForIn.toList_rci r) init
      (fun a ha b => f a (Rci.mem_toList_iff_mem.mp ha) b)).trans
        Rci.forIn'_toList_eq_forIn').symm

instance {m : Type u → Type v} [Monad m] [LawfulMonad m] : PureForIn m (Rci α) α where
  forIn_eq r init f := by
    show forIn' r init (fun a _ b => f a b) = _
    rw [PureForIn'.forIn'_eq (m := m)]
    exact forIn'_eq_forIn _ _ _ _ (fun _ _ _ => rfl)

end Rci

section Roc
variable {α : Type u} [LE α] [DecidableLE α] [LT α] [DecidableLT α] [UpwardEnumerable α] [Rxc.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α]

omit [DecidableLT α] in
theorem ForIn.toList_roc (r : Roc α) : ForIn.toList r = r.toList := by
  simp only [ForIn.toList, ForIn.toArray, Id.run, forIn, Roc.forIn'_eq_forIn'_toList,
    List.forIn'_pure_yield_eq_foldl]
  change (List.foldl (fun acc a => acc.push a.val) #[] r.toList.attach).toList = r.toList
  rw [← List.foldl_map (f := Subtype.val) (g := fun acc a => Array.push acc a),
    List.attach_map_subtype_val, foldl_push_toList]
  simp

instance : LawfulMemForInId (Roc α) α where
  mem_toList_iff {_a _r} := by rw [ForIn.toList_roc]; exact Roc.mem_toList_iff_mem

instance {m : Type u → Type v} [Monad m] [LawfulMonad m] : PureForIn' m (Roc α) α where
  forIn'_eq r init f :=
    ((forIn'_cast (ForIn.toList_roc r) init
      (fun a ha b => f a (Roc.mem_toList_iff_mem.mp ha) b)).trans
        Roc.forIn'_toList_eq_forIn').symm

instance {m : Type u → Type v} [Monad m] [LawfulMonad m] : PureForIn m (Roc α) α where
  forIn_eq r init f := by
    show forIn' r init (fun a _ b => f a b) = _
    rw [PureForIn'.forIn'_eq (m := m)]
    exact forIn'_eq_forIn _ _ _ _ (fun _ _ _ => rfl)

end Roc

section Roo
variable {α : Type u} [LT α] [DecidableLT α] [UpwardEnumerable α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]

theorem ForIn.toList_roo (r : Roo α) : ForIn.toList r = r.toList := by
  simp only [ForIn.toList, ForIn.toArray, Id.run, forIn, Roo.forIn'_eq_forIn'_toList,
    List.forIn'_pure_yield_eq_foldl]
  change (List.foldl (fun acc a => acc.push a.val) #[] r.toList.attach).toList = r.toList
  rw [← List.foldl_map (f := Subtype.val) (g := fun acc a => Array.push acc a),
    List.attach_map_subtype_val, foldl_push_toList]
  simp

instance : LawfulMemForInId (Roo α) α where
  mem_toList_iff {_a _r} := by rw [ForIn.toList_roo]; exact Roo.mem_toList_iff_mem

instance {m : Type u → Type v} [Monad m] [LawfulMonad m] : PureForIn' m (Roo α) α where
  forIn'_eq r init f :=
    ((forIn'_cast (ForIn.toList_roo r) init
      (fun a ha b => f a (Roo.mem_toList_iff_mem.mp ha) b)).trans
        Roo.forIn'_toList_eq_forIn').symm

instance {m : Type u → Type v} [Monad m] [LawfulMonad m] : PureForIn m (Roo α) α where
  forIn_eq r init f := by
    show forIn' r init (fun a _ b => f a b) = _
    rw [PureForIn'.forIn'_eq (m := m)]
    exact forIn'_eq_forIn _ _ _ _ (fun _ _ _ => rfl)

end Roo

section Roi
variable {α : Type u} [LT α] [DecidableLT α] [UpwardEnumerable α] [Rxi.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]

omit [DecidableLT α] in
theorem ForIn.toList_roi (r : Roi α) : ForIn.toList r = r.toList := by
  simp only [ForIn.toList, ForIn.toArray, Id.run, forIn, Roi.forIn'_eq_forIn'_toList,
    List.forIn'_pure_yield_eq_foldl]
  change (List.foldl (fun acc a => acc.push a.val) #[] r.toList.attach).toList = r.toList
  rw [← List.foldl_map (f := Subtype.val) (g := fun acc a => Array.push acc a),
    List.attach_map_subtype_val, foldl_push_toList]
  simp

instance : LawfulMemForInId (Roi α) α where
  mem_toList_iff {_a _r} := by rw [ForIn.toList_roi]; exact Roi.mem_toList_iff_mem

instance {m : Type u → Type v} [Monad m] [LawfulMonad m] : PureForIn' m (Roi α) α where
  forIn'_eq r init f :=
    ((forIn'_cast (ForIn.toList_roi r) init
      (fun a ha b => f a (Roi.mem_toList_iff_mem.mp ha) b)).trans
        Roi.forIn'_toList_eq_forIn').symm

instance {m : Type u → Type v} [Monad m] [LawfulMonad m] : PureForIn m (Roi α) α where
  forIn_eq r init f := by
    show forIn' r init (fun a _ b => f a b) = _
    rw [PureForIn'.forIn'_eq (m := m)]
    exact forIn'_eq_forIn _ _ _ _ (fun _ _ _ => rfl)

end Roi

section Ric
variable {α : Type u} [Least? α] [LE α] [DecidableLE α] [UpwardEnumerable α] [Rxc.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLeast? α] [LawfulUpwardEnumerableLE α]

theorem ForIn.toList_ric (r : Ric α) : ForIn.toList r = r.toList := by
  simp only [ForIn.toList, ForIn.toArray, Id.run, forIn, Ric.forIn'_eq_forIn'_toList,
    List.forIn'_pure_yield_eq_foldl]
  change (List.foldl (fun acc a => acc.push a.val) #[] r.toList.attach).toList = r.toList
  rw [← List.foldl_map (f := Subtype.val) (g := fun acc a => Array.push acc a),
    List.attach_map_subtype_val, foldl_push_toList]
  simp

instance : LawfulMemForInId (Ric α) α where
  mem_toList_iff {_a _r} := by rw [ForIn.toList_ric]; exact Ric.mem_toList_iff_mem

instance {m : Type u → Type v} [Monad m] [LawfulMonad m] : PureForIn' m (Ric α) α where
  forIn'_eq r init f :=
    ((forIn'_cast (ForIn.toList_ric r) init
      (fun a ha b => f a (Ric.mem_toList_iff_mem.mp ha) b)).trans
        Ric.forIn'_toList_eq_forIn').symm

instance {m : Type u → Type v} [Monad m] [LawfulMonad m] : PureForIn m (Ric α) α where
  forIn_eq r init f := by
    show forIn' r init (fun a _ b => f a b) = _
    rw [PureForIn'.forIn'_eq (m := m)]
    exact forIn'_eq_forIn _ _ _ _ (fun _ _ _ => rfl)

end Ric

section Rio
variable {α : Type u} [Least? α] [LT α] [DecidableLT α] [UpwardEnumerable α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLeast? α] [LawfulUpwardEnumerableLT α]

theorem ForIn.toList_rio (r : Rio α) : ForIn.toList r = r.toList := by
  simp only [ForIn.toList, ForIn.toArray, Id.run, forIn, Rio.forIn'_eq_forIn'_toList,
    List.forIn'_pure_yield_eq_foldl]
  change (List.foldl (fun acc a => acc.push a.val) #[] r.toList.attach).toList = r.toList
  rw [← List.foldl_map (f := Subtype.val) (g := fun acc a => Array.push acc a),
    List.attach_map_subtype_val, foldl_push_toList]
  simp

instance : LawfulMemForInId (Rio α) α where
  mem_toList_iff {_a _r} := by rw [ForIn.toList_rio]; exact Rio.mem_toList_iff_mem

instance {m : Type u → Type v} [Monad m] [LawfulMonad m] : PureForIn' m (Rio α) α where
  forIn'_eq r init f :=
    ((forIn'_cast (ForIn.toList_rio r) init
      (fun a ha b => f a (Rio.mem_toList_iff_mem.mp ha) b)).trans
        Rio.forIn'_toList_eq_forIn').symm

instance {m : Type u → Type v} [Monad m] [LawfulMonad m] : PureForIn m (Rio α) α where
  forIn_eq r init f := by
    show forIn' r init (fun a _ b => f a b) = _
    rw [PureForIn'.forIn'_eq (m := m)]
    exact forIn'_eq_forIn _ _ _ _ (fun _ _ _ => rfl)

end Rio

section Rii
variable {α : Type u} [LT α] [Least? α] [UpwardEnumerable α] [Rxi.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLeast? α] [LawfulUpwardEnumerableLT α]

omit [LT α] [LawfulUpwardEnumerableLT α] in
theorem ForIn.toList_rii (r : Rii α) : ForIn.toList r = r.toList := by
  simp only [ForIn.toList, ForIn.toArray, Id.run, forIn, Rii.forIn'_eq_forIn'_toList,
    List.forIn'_pure_yield_eq_foldl]
  change (List.foldl (fun acc a => acc.push a.val) #[] r.toList.attach).toList = r.toList
  rw [← List.foldl_map (f := Subtype.val) (g := fun acc a => Array.push acc a),
    List.attach_map_subtype_val, foldl_push_toList]
  simp

instance : LawfulMemForInId (Rii α) α where
  mem_toList_iff {_a _r} := by rw [ForIn.toList_rii]; exact ⟨fun _ => trivial, fun _ => Rii.mem_toList⟩

instance {m : Type u → Type v} [Monad m] [LawfulMonad m] : PureForIn' m (Rii α) α where
  forIn'_eq r init f :=
    ((forIn'_cast (ForIn.toList_rii r) init
      (fun a _ha b => f a trivial b)).trans
        Rii.forIn'_toList_eq_forIn').symm

instance {m : Type u → Type v} [Monad m] [LawfulMonad m] : PureForIn m (Rii α) α where
  forIn_eq r init f := by
    show forIn' r init (fun a _ b => f a b) = _
    rw [PureForIn'.forIn'_eq (m := m)]
    exact forIn'_eq_forIn _ _ _ _ (fun _ _ _ => rfl)

end Rii

end PRange

section Slice

open Std.Iterators in
/-- `ForIn.toList` on a slice is the slice's own `toList`. -/
@[simp, grind =] theorem ForIn.toList_slice {γ : Type u} {α γ' : Type w}
    [ToIterator (Slice γ) Id α γ'] [Iterator α Id γ'] [Finite α Id]
    [IteratorLoop α Id Id] [LawfulIteratorLoop α Id Id] (s : Slice γ) :
    ForIn.toList s = s.toList := by
  simp only [ForIn.toList, ForIn.toArray, Id.run, ← Slice.forIn_toList,
    List.forIn_pure_yield_eq_foldl]
  change (List.foldl (fun acc a => acc.push a) #[] s.toList).toList = s.toList
  rw [foldl_push_toList]; simp

open Std.Iterators in
instance {γ : Type u} {α γ' : Type w} {m : Type w → Type v} [Monad m] [LawfulMonad m]
    [ToIterator (Slice γ) Id α γ'] [Iterator α Id γ'] [Finite α Id]
    [IteratorLoop α Id m] [LawfulIteratorLoop α Id m]
    [IteratorLoop α Id Id] [LawfulIteratorLoop α Id Id] :
    PureForIn m (Slice γ) γ' where
  forIn_eq s init f := by rw [ForIn.toList_slice]; exact Slice.forIn_toList.symm

end Slice

end Std.Internal
