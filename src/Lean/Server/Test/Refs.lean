/-
Copyright (c) 2025 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga
-/
module

prelude
import Init.Prelude

-- This needs to be top-level, but the only way to get this is to do the all-encompassing
-- `import Lean`, so we just accept the pollution.
set_option linter.coreInternal.internalModule false in
public def LeanServerTestRefsTest0 := Nat

public def Lean.Server.Test.LeanServerTestRefsTest0' := Nat

namespace Lean.Server.Test.Refs

public def Test1 := Nat
public def Test2 := Test1
public def Test3 := Test1
public def Test4 := Test2
public def Test5 := Test2

public inductive Test6
  | mk
public def test7 : Test6 := .mk
public def test8 : Test6 := .mk
public def test9 := test7
public def test10 := test9
