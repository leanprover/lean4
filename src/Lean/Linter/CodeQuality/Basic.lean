/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/

module

prelude

public import Init.Data.Float
public import Std.Data.TreeMap
public import Init.Data.Ord
public import Lean.Data.Json

public section

namespace Lean.Linter.CodeQuality

inductive Source where
  | module (name : Name)
  | declaration (module : Name) (name : Name)
  deriving ToJson

inductive Value where
  | scalar (value : Float)
  | dict (dictionary : Std.TreeMap String Float)
  deriving ToJson

structure Entry where
  name : String
  source : Source
  value : Value
  deriving ToJson

end Lean.Linter.CodeQuality
