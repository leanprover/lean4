/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Init.Data.String.Basic
import Init.Data.String.Modify
import Init.Data.String.Search
import Init.Data.Iterators.Consumers.Collect

namespace Lake

open Lean (Name)

/-- Converts a snake case, kebab case, or lower camel case `String` to upper camel case. -/
public def toUpperCamelCaseString (str : String) : String :=
  let parts := str.split fun chr => chr == '_' || chr == '-'
  String.join <| parts.map (·.copy.capitalize) |>.toList

/-- Converts a snake case, kebab case, or lower camel case `Name` to upper camel case. -/
public def toUpperCamelCase (name : Name) : Name :=
  if let Name.str p s := name then
    Name.mkStr (toUpperCamelCase p) <| toUpperCamelCaseString s
  else
    name
