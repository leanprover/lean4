/-
Copyright (c) 2025 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga
-/
module

prelude
import Init.Prelude

namespace Lean.Server.Test.Refs

public def Test1 := Nat
public def Test2 := Test1
public def Test3 := Test1
public def Test4 := Test2
public def Test5 := Test2
