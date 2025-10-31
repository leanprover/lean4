/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Std.Data.Iterators.Producers.Range
import Init.Data.Range.Polymorphic.Lemmas

@[expose] public section

namespace Std
open Std.PRange Std.Iterators

@[simp]
theorem Rcc.toList_iter_eq_toList [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Rcc α} :
    r.iter.toList = r.toList := by
 rfl

@[simp]
theorem Rcc.toArray_iter_eq_toArray [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Rcc α} :
    r.iter.toArray = r.toArray := by
 rfl

@[simp]
theorem Rcc.count_iter_eq_size [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [Rxc.HasSize α] [Rxc.LawfulHasSize α]
    {r : Rcc α} :
    r.iter.count = r.size := by
  rw [← size_toArray, ← toArray_iter_eq_toArray, Iter.size_toArray_eq_count]

@[simp]
theorem Rco.toList_iter_eq_toList [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Rco α} :
    r.iter.toList = r.toList := by
 rfl

@[simp]
theorem Rco.toArray_iter_eq_toArray [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Rco α} :
    r.iter.toArray = r.toArray := by
 rfl

@[simp]
theorem Rco.count_iter_eq_size [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [Rxo.HasSize α] [Rxo.LawfulHasSize α]
    {r : Rco α} :
    r.iter.count = r.size := by
  rw [← size_toArray, ← toArray_iter_eq_toArray, Iter.size_toArray_eq_count]

@[simp]
theorem Rci.toList_iter_eq_toList [UpwardEnumerable α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Rci α} :
    r.iter.toList = r.toList := by
 rfl

@[simp]
theorem Rci.toArray_iter_eq_toArray [UpwardEnumerable α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Rci α} :
    r.iter.toArray = r.toArray := by
 rfl

@[simp]
theorem Rci.count_iter_eq_size [UpwardEnumerable α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [Rxi.HasSize α] [Rxi.LawfulHasSize α]
    {r : Rci α} :
    r.iter.count = r.size := by
  rw [← size_toArray, ← toArray_iter_eq_toArray, Iter.size_toArray_eq_count]

@[simp]
theorem Roc.toList_iter_eq_toList [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Roc α} :
    r.iter.toList = r.toList := by
 rfl

@[simp]
theorem Roc.toArray_iter_eq_toArray [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Roc α} :
    r.iter.toArray = r.toArray := by
 rfl

@[simp]
theorem Roc.count_iter_eq_size [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [Rxc.HasSize α] [Rxc.LawfulHasSize α]
    {r : Roc α} :
    r.iter.count = r.size := by
  rw [← size_toArray, ← toArray_iter_eq_toArray, Iter.size_toArray_eq_count]

@[simp]
theorem Roo.toList_iter_eq_toList [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Roo α} :
    r.iter.toList = r.toList := by
 rfl

@[simp]
theorem Roo.toArray_iter_eq_toArray [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Roo α} :
    r.iter.toArray = r.toArray := by
 rfl

@[simp]
theorem Roo.count_iter_eq_size [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [Rxo.HasSize α] [Rxo.LawfulHasSize α]
    {r : Roo α} :
    r.iter.count = r.size := by
  rw [← size_toArray, ← toArray_iter_eq_toArray, Iter.size_toArray_eq_count]

@[simp]
theorem Roi.toList_iter_eq_toList [UpwardEnumerable α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Roi α} :
    r.iter.toList = r.toList := by
 rfl

@[simp]
theorem Roi.toArray_iter_eq_toArray [UpwardEnumerable α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Roi α} :
    r.iter.toArray = r.toArray := by
 rfl

@[simp]
theorem Roi.count_iter_eq_size [UpwardEnumerable α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [Rxi.HasSize α] [Rxi.LawfulHasSize α]
    {r : Roi α} :
    r.iter.count = r.size := by
  rw [← size_toArray, ← toArray_iter_eq_toArray, Iter.size_toArray_eq_count]

@[simp]
theorem Ric.toList_iter_eq_toList [Least? α] [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Ric α} :
    r.iter.toList = r.toList := by
 rfl

@[simp]
theorem Ric.toArray_iter_eq_toArray [Least? α] [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Ric α} :
    r.iter.toArray = r.toArray := by
 rfl

@[simp]
theorem Ric.count_iter_eq_size [Least? α] [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [Rxc.HasSize α] [Rxc.LawfulHasSize α]
    {r : Ric α} :
    r.iter.count = r.size := by
  rw [← size_toArray, ← toArray_iter_eq_toArray, Iter.size_toArray_eq_count]

@[simp]
theorem Rio.toList_iter_eq_toList [Least? α] [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Rio α} :
    r.iter.toList = r.toList := by
 rfl

@[simp]
theorem Rio.toArray_iter_eq_toArray [Least? α] [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Rio α} :
    r.iter.toArray = r.toArray := by
 rfl

@[simp]
theorem Rio.count_iter_eq_size [Least? α] [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [Rxo.HasSize α] [Rxo.LawfulHasSize α]
    {r : Rio α} :
    r.iter.count = r.size := by
  rw [← size_toArray, ← toArray_iter_eq_toArray, Iter.size_toArray_eq_count]

@[simp]
theorem Rii.toList_iter_eq_toList [Least? α] [UpwardEnumerable α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Rii α} :
    r.iter.toList = r.toList := by
 rfl

@[simp]
theorem Rii.toArray_iter_eq_toArray [Least? α] [UpwardEnumerable α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Rii α} :
    r.iter.toArray = r.toArray := by
 rfl

@[simp]
theorem Rii.count_iter_eq_size [Least? α] [UpwardEnumerable α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [Rxi.HasSize α] [Rxi.LawfulHasSize α]
    {r : Rii α} :
    r.iter.count = r.size := by
  rw [← size_toArray, ← toArray_iter_eq_toArray, Iter.size_toArray_eq_count]

end Std
