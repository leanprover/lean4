/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
module

prelude
public import Lean.Data.NameMap.Basic
public import Std.Data.TreeSet.AdditionalOperations

public section

namespace Lean
namespace NameMap

/-- `filterMap f m` filters an `NameMap` and simultaneously modifies the filtered values.

It takes a function `f : Name → α → Option β` and applies `f name` to the value with key `name`.
The resulting entries with non-`none` value are collected to form the output `NameMap`. -/
def filterMap (f : Name → α → Option β) (m : NameMap α) : NameMap β := Std.TreeMap.filterMap f m

end NameMap
end Lean
