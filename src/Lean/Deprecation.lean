/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.ImportingFlag
public import Lean.Data.KVMap
public import Lean.Data.NameMap.Basic

namespace Lean.Linter


/-!
Datastructures common to deprecation features.
-/

public structure DeprecationEntry where
  newName? : Option Name := none
  text? : Option String := none
  since? : Option String := none
  deriving Inhabited
