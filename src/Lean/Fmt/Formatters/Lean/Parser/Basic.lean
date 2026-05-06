/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Lean.Parser.Basic
import Init.Data

namespace Lean.Fmt

@[builtin_fmt fieldIdx]
public def fmtFieldIdx : Fmt := fmtAtomic
