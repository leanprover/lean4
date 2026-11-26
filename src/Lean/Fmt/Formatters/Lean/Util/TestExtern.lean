/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Lean.Util.TestExtern
import Init.Data

namespace Lean.Fmt

@[builtin_fmt Lean.testExternCmd]
public def fmtTestExtern : Fmt := fun
  | `(Lean.testExternCmd| test_extern%$testExternTk $t:term) => do
    let testExternTk ← fmt testExternTk
    let t ← fmt t
    return Layouts.pseudoApplication #[testExternTk, t]
  | _ => throw .partialFormatter
