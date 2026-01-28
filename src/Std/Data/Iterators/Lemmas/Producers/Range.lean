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
theorem Rcc.toList_iter [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Rcc α} :
    r.iter.toList = r.toList := by
 rfl

@[deprecated Rcc.toList_iter (since := "2025-11-13")]
theorem Rcc.toList_iter_eq_toList [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Rcc α} :
    r.iter.toList = r.toList := by
 rfl

@[simp]
theorem Rcc.toArray_iter [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Rcc α} :
    r.iter.toArray = r.toArray := by
 rfl

@[deprecated Rcc.toArray_iter (since := "2025-11-13")]
theorem Rcc.toArray_iter_eq_toArray [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Rcc α} :
    r.iter.toArray = r.toArray := by
 rfl

@[simp]
theorem Rcc.length_iter [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [Rxc.HasSize α] [Rxc.LawfulHasSize α] {r : Rcc α} :
    r.iter.length = r.size := by
  rw [← size_toArray, ← toArray_iter, Iter.size_toArray_eq_length]

@[deprecated Rcc.length_iter (since := "2026-01-28")]
theorem Rcc.count_iter [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [Rxc.HasSize α] [Rxc.LawfulHasSize α] {r : Rcc α} :
    r.iter.length = r.size :=
  length_iter

@[deprecated Rcc.length_iter (since := "2025-11-13")]
theorem Rcc.count_iter_eq_size [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [Rxc.HasSize α] [Rxc.LawfulHasSize α]
    {r : Rcc α} :
    r.iter.length = r.size :=
  length_iter

@[simp]
theorem Rco.toList_iter [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Rco α} :
    r.iter.toList = r.toList := by
 rfl

@[deprecated Rco.toList_iter (since := "2025-11-13")]
theorem Rco.toList_iter_eq_toList [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Rco α} :
    r.iter.toList = r.toList := by
 rfl

@[simp]
theorem Rco.toArray_iter [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Rco α} :
    r.iter.toArray = r.toArray := by
 rfl

@[deprecated Rco.toArray_iter (since := "2025-11-13")]
theorem Rco.toArray_iter_eq_toArray [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Rco α} :
    r.iter.toArray = r.toArray := by
 rfl

@[simp]
theorem Rco.length_iter [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [Rxo.HasSize α] [Rxo.LawfulHasSize α]
    {r : Rco α} :
    r.iter.length = r.size := by
  rw [← size_toArray, ← toArray_iter, Iter.size_toArray_eq_length]

@[deprecated Rco.length_iter (since := "2026-01-28")]
theorem Rco.count_iter [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [Rxo.HasSize α] [Rxo.LawfulHasSize α]
    {r : Rco α} :
    r.iter.length = r.size := by
  rw [← size_toArray, ← toArray_iter, Iter.size_toArray_eq_length]

@[deprecated Rco.length_iter (since := "2025-11-13")]
theorem Rco.count_iter_eq_size [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [Rxo.HasSize α] [Rxo.LawfulHasSize α]
    {r : Rco α} :
    r.iter.length = r.size := by
  rw [← size_toArray, ← toArray_iter, Iter.size_toArray_eq_length]

@[simp]
theorem Rci.toList_iter [UpwardEnumerable α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Rci α} :
    r.iter.toList = r.toList := by
 rfl

@[deprecated Rci.toList_iter (since := "2025-11-13")]
theorem Rci.toList_iter_eq_toList [UpwardEnumerable α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Rci α} :
    r.iter.toList = r.toList := by
 rfl

@[simp]
theorem Rci.toArray_iter [UpwardEnumerable α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Rci α} :
    r.iter.toArray = r.toArray := by
 rfl

@[simp]
theorem Rci.toArray_iter_eq_toArray [UpwardEnumerable α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Rci α} :
    r.iter.toArray = r.toArray := by
 rfl

@[simp]
theorem Rci.length_iter [UpwardEnumerable α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [Rxi.HasSize α] [Rxi.LawfulHasSize α]
    {r : Rci α} :
    r.iter.length = r.size := by
  rw [← size_toArray, ← toArray_iter_eq_toArray, Iter.size_toArray_eq_length]

@[deprecated Rci.length_iter (since := "2026-01-28")]
theorem Rci.count_iter [UpwardEnumerable α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [Rxi.HasSize α] [Rxi.LawfulHasSize α]
    {r : Rci α} :
    r.iter.length = r.size := by
  rw [← size_toArray, ← toArray_iter_eq_toArray, Iter.size_toArray_eq_length]

@[deprecated Rci.length_iter (since := "2025-11-13")]
theorem Rci.count_iter_eq_size [UpwardEnumerable α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [Rxi.HasSize α] [Rxi.LawfulHasSize α]
    {r : Rci α} :
    r.iter.length = r.size := by
  rw [← size_toArray, ← toArray_iter_eq_toArray, Iter.size_toArray_eq_length]

@[simp]
theorem Roc.toList_iter [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Roc α} :
    r.iter.toList = r.toList := by
 rfl

@[deprecated Roc.toList_iter (since := "2025-11-13")]
theorem Roc.toList_iter_eq_toList [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Roc α} :
    r.iter.toList = r.toList := by
 rfl

@[simp]
theorem Roc.toArray_iter [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Roc α} :
    r.iter.toArray = r.toArray := by
 rfl

@[simp]
theorem Roc.toArray_iter_eq_toArray [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Roc α} :
    r.iter.toArray = r.toArray := by
 rfl

@[simp]
theorem Roc.length_iter [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [Rxc.HasSize α] [Rxc.LawfulHasSize α]
    {r : Roc α} :
    r.iter.length = r.size := by
  rw [← size_toArray, ← toArray_iter_eq_toArray, Iter.size_toArray_eq_length]

@[deprecated Roc.length_iter (since := "2026-01-28")]
theorem Roc.count_iter [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [Rxc.HasSize α] [Rxc.LawfulHasSize α]
    {r : Roc α} :
    r.iter.length = r.size := by
  rw [← size_toArray, ← toArray_iter_eq_toArray, Iter.size_toArray_eq_length]

@[deprecated Roc.length_iter (since := "2025-11-13")]
theorem Roc.count_iter_eq_size [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [Rxc.HasSize α] [Rxc.LawfulHasSize α]
    {r : Roc α} :
    r.iter.length = r.size := by
  rw [← size_toArray, ← toArray_iter_eq_toArray, Iter.size_toArray_eq_length]

@[simp]
theorem Roo.toList_iter [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Roo α} :
    r.iter.toList = r.toList := by
 rfl

@[deprecated Roo.toList_iter (since := "2025-11-13")]
theorem Roo.toList_iter_eq_toList [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Roo α} :
    r.iter.toList = r.toList := by
 rfl

@[simp]
theorem Roo.toArray_iter [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Roo α} :
    r.iter.toArray = r.toArray := by
 rfl

@[simp]
theorem Roo.toArray_iter_eq_toArray [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Roo α} :
    r.iter.toArray = r.toArray := by
 rfl

@[simp]
theorem Roo.length_iter [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [Rxo.HasSize α] [Rxo.LawfulHasSize α]
    {r : Roo α} :
    r.iter.length = r.size := by
  rw [← size_toArray, ← toArray_iter_eq_toArray, Iter.size_toArray_eq_length]

@[deprecated Roo.length_iter (since := "2026-01-28")]
theorem Roo.count_iter [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [Rxo.HasSize α] [Rxo.LawfulHasSize α]
    {r : Roo α} :
    r.iter.length = r.size := by
  rw [← size_toArray, ← toArray_iter_eq_toArray, Iter.size_toArray_eq_length]

@[deprecated Roo.length_iter (since := "2025-11-13")]
theorem Roo.count_iter_eq_size [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [Rxo.HasSize α] [Rxo.LawfulHasSize α]
    {r : Roo α} :
    r.iter.length = r.size := by
  rw [← size_toArray, ← toArray_iter_eq_toArray, Iter.size_toArray_eq_length]

@[simp]
theorem Roi.toList_iter [UpwardEnumerable α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Roi α} :
    r.iter.toList = r.toList := by
 rfl

@[deprecated Roi.toList_iter (since := "2025-11-13")]
theorem Roi.toList_iter_eq_toList [UpwardEnumerable α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Roi α} :
    r.iter.toList = r.toList := by
 rfl

@[simp]
theorem Roi.toArray_iter [UpwardEnumerable α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Roi α} :
    r.iter.toArray = r.toArray := by
 rfl

@[deprecated Roi.toArray_iter (since := "2025-11-13")]
theorem Roi.toArray_iter_eq_toArray [UpwardEnumerable α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Roi α} :
    r.iter.toArray = r.toArray := by
 rfl

@[simp]
theorem Roi.length_iter [UpwardEnumerable α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [Rxi.HasSize α] [Rxi.LawfulHasSize α]
    {r : Roi α} :
    r.iter.length = r.size := by
  rw [← size_toArray, ← toArray_iter, Iter.size_toArray_eq_length]

@[deprecated Roi.length_iter (since := "2026-01-28")]
theorem Roi.count_iter [UpwardEnumerable α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [Rxi.HasSize α] [Rxi.LawfulHasSize α]
    {r : Roi α} :
    r.iter.length = r.size := by
  rw [← size_toArray, ← toArray_iter, Iter.size_toArray_eq_length]

@[deprecated Roi.length_iter (since := "2025-11-13")]
theorem Roi.count_iter_eq_size [UpwardEnumerable α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [Rxi.HasSize α] [Rxi.LawfulHasSize α]
    {r : Roi α} :
    r.iter.length = r.size := by
  rw [← size_toArray, ← toArray_iter, Iter.size_toArray_eq_length]

@[simp]
theorem Ric.toList_iter [Least? α] [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Ric α} :
    r.iter.toList = r.toList := by
 rfl

@[deprecated Ric.toList_iter (since := "2025-11-13")]
theorem Ric.toList_iter_eq_toList [Least? α] [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Ric α} :
    r.iter.toList = r.toList := by
 rfl

@[simp]
theorem Ric.toArray_iter [Least? α] [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Ric α} :
    r.iter.toArray = r.toArray := by
 rfl

@[deprecated Ric.toArray_iter (since := "2025-11-13")]
theorem Ric.toArray_iter_eq_toArray [Least? α] [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Ric α} :
    r.iter.toArray = r.toArray := by
 rfl

@[simp]
theorem Ric.length_iter [Least? α] [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [Rxc.HasSize α] [Rxc.LawfulHasSize α]
    {r : Ric α} :
    r.iter.length = r.size := by
  rw [← size_toArray, ← toArray_iter, Iter.size_toArray_eq_length]

@[deprecated Ric.length_iter (since := "2026-01-28")]
theorem Ric.count_iter [Least? α] [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [Rxc.HasSize α] [Rxc.LawfulHasSize α]
    {r : Ric α} :
    r.iter.length = r.size := by
  rw [← size_toArray, ← toArray_iter, Iter.size_toArray_eq_length]

@[deprecated Ric.length_iter (since := "2025-11-13")]
theorem Ric.count_iter_eq_size [Least? α] [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [Rxc.HasSize α] [Rxc.LawfulHasSize α]
    {r : Ric α} :
    r.iter.length = r.size := by
  rw [← size_toArray, ← toArray_iter, Iter.size_toArray_eq_length]

@[simp]
theorem Rio.toList_iter [Least? α] [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Rio α} :
    r.iter.toList = r.toList := by
 rfl

@[deprecated Rio.toList_iter (since := "2025-11-13")]
theorem Rio.toList_iter_eq_toList [Least? α] [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Rio α} :
    r.iter.toList = r.toList := by
 rfl

@[simp]
theorem Rio.toArray_iter [Least? α] [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Rio α} :
    r.iter.toArray = r.toArray := by
 rfl

@[deprecated Rio.toArray_iter (since := "2025-11-13")]
theorem Rio.toArray_iter_eq_toArray [Least? α] [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Rio α} :
    r.iter.toArray = r.toArray := by
 rfl

@[simp]
theorem Rio.length_iter [Least? α] [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [Rxo.HasSize α] [Rxo.LawfulHasSize α]
    {r : Rio α} :
    r.iter.length = r.size := by
  rw [← size_toArray, ← toArray_iter, Iter.size_toArray_eq_length]

@[deprecated Rio.length_iter (since := "2026-01-28")]
theorem Rio.count_iter [Least? α] [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [Rxo.HasSize α] [Rxo.LawfulHasSize α]
    {r : Rio α} :
    r.iter.length = r.size := by
  rw [← size_toArray, ← toArray_iter, Iter.size_toArray_eq_length]

@[deprecated Rio.length_iter (since := "2025-11-13")]
theorem Rio.count_iter_eq_size [Least? α] [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [Rxo.HasSize α] [Rxo.LawfulHasSize α]
    {r : Rio α} :
    r.iter.length = r.size := by
  rw [← size_toArray, ← toArray_iter, Iter.size_toArray_eq_length]

@[simp]
theorem Rii.toList_iter [Least? α] [UpwardEnumerable α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Rii α} :
    r.iter.toList = r.toList := by
 rfl

@[deprecated Rii.toList_iter (since := "2025-11-13")]
theorem Rii.toList_iter_eq_toList [Least? α] [UpwardEnumerable α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Rii α} :
    r.iter.toList = r.toList := by
 rfl

@[simp]
theorem Rii.toArray_iter [Least? α] [UpwardEnumerable α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Rii α} :
    r.iter.toArray = r.toArray := by
 rfl

@[deprecated Rii.toArray_iter (since := "2025-11-13")]
theorem Rii.toArray_iter_eq_toArray [Least? α] [UpwardEnumerable α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Rii α} :
    r.iter.toArray = r.toArray := by
 rfl

@[simp]
theorem Rii.length_iter [Least? α] [UpwardEnumerable α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [Rxi.HasSize α] [Rxi.LawfulHasSize α]
    {r : Rii α} :
    r.iter.length = r.size := by
  rw [← size_toArray, ← toArray_iter, Iter.size_toArray_eq_length]

@[deprecated Rii.length_iter (since := "2026-01-28")]
theorem Rii.count_iter [Least? α] [UpwardEnumerable α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [Rxi.HasSize α] [Rxi.LawfulHasSize α]
    {r : Rii α} :
    r.iter.length = r.size := by
  rw [← size_toArray, ← toArray_iter, Iter.size_toArray_eq_length]

@[deprecated Rii.length_iter (since := "2025-11-13")]
theorem Rii.count_iter_eq_size [Least? α] [UpwardEnumerable α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [Rxi.HasSize α] [Rxi.LawfulHasSize α]
    {r : Rii α} :
    r.iter.length = r.size := by
  rw [← size_toArray, ← toArray_iter, Iter.size_toArray_eq_length]

end Std
