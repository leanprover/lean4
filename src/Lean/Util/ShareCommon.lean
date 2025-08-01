/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.ShareCommon
public import Std.Data.HashSet.Basic
public import Std.Data.HashMap.Basic
public import Lean.Data.PersistentHashMap
public import Lean.Data.PersistentHashSet

public section

open ShareCommon
namespace Lean.ShareCommon

def objectFactory :=
  StateFactory.mk {
    Map := Std.HashMap, mkMap := (Std.HashMap.emptyWithCapacity ·), mapFind? := (·.get?), mapInsert := (·.insert)
    Set := Std.HashSet, mkSet := (Std.HashSet.emptyWithCapacity ·), setFind? := (·.get?), setInsert := (·.insert)
  }

def persistentObjectFactory :=
  StateFactory.mk {
    Map := PersistentHashMap, mkMap := fun _ => .empty, mapFind? := (·.find?), mapInsert := (·.insert)
    Set := PersistentHashSet, mkSet := fun _ => .empty, setFind? := (·.find?), setInsert := (·.insert)
  }

abbrev ShareCommonT := _root_.ShareCommonT objectFactory
abbrev PShareCommonT := _root_.ShareCommonT persistentObjectFactory
abbrev ShareCommonM := ShareCommonT Id
abbrev PShareCommonM := PShareCommonT Id

@[specialize] def ShareCommonT.withShareCommon [Monad m] (a : α) : ShareCommonT m α :=
  modifyGet fun s => s.shareCommon a

@[specialize] def PShareCommonT.withShareCommon [Monad m] (a : α) : PShareCommonT m α :=
  modifyGet fun s => s.shareCommon a

instance ShareCommonT.monadShareCommon [Monad m] : MonadShareCommon (ShareCommonT m) where
  withShareCommon := ShareCommonT.withShareCommon

instance PShareCommonT.monadShareCommon [Monad m] : MonadShareCommon (PShareCommonT m) where
  withShareCommon := PShareCommonT.withShareCommon

@[inline] def ShareCommonT.run [Monad m] : ShareCommonT m α → m α := _root_.ShareCommonT.run
@[inline] def PShareCommonT.run [Monad m] : PShareCommonT m α → m α := _root_.ShareCommonT.run
@[inline] def ShareCommonM.run : ShareCommonM α → α := ShareCommonT.run
@[inline] def PShareCommonM.run : PShareCommonM α → α := PShareCommonT.run

def shareCommon (a : α) : α := (withShareCommon a : ShareCommonM α).run
