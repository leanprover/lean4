/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Gabriel Ebner, Marc Huisinga
-/
module

prelude
public import Lean.Data.Json.FromToJson.Basic
public import Std.Data.TreeMap.AdditionalOperations

public section

/-
This module exists to cut the dependency on `Std.Data.TreeMap.AdditionalOperations` from a large
chunk of the meta framework.
-/

namespace Lean

private def TreeMap.toJson [ToJson α] (map : Std.TreeMap String α compare) : Json :=
  let json := Std.TreeMap.map (fun _ => Lean.toJson) <| map
  -- TODO(henrik): remove this after Q4
  Json.obj <| Std.TreeMap.Raw.mk <| Std.DTreeMap.Raw.mk json.inner.inner

private def TreeMap.fromJson? {cmp} [FromJson α] (j : Json) :
    Except String (Std.TreeMap String α cmp) := do
  let o ← j.getObj?
  o.foldlM (fun x k v => x.insert k <$> Lean.fromJson? v) ∅

instance [ToJson α] : ToJson (Std.TreeMap String α compare) where
  toJson := private TreeMap.toJson

instance {cmp} [FromJson α] : FromJson (Std.TreeMap String α cmp) where
  fromJson? := private TreeMap.fromJson?


end Lean
