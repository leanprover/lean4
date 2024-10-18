/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.ShareCommon
import Std.Data.HashSet
import Std.Data.HashMap
import Lean.Data.PersistentHashMap
import Lean.Data.PersistentHashSet

open ShareCommon
namespace Lean.ShareCommon

def objectFactory :=
  StateFactory.mk {
    Map := Std.HashMap, mkMap := (Std.HashMap.empty ·), mapFind? := (·.get?), mapInsert := (·.insert)
    Set := Std.HashSet, mkSet := (Std.HashSet.empty ·), setFind? := (·.get?), setInsert := (·.insert)
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
