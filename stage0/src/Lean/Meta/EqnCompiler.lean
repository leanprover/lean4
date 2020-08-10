/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.EqnCompiler.MatchPattern
import Lean.Meta.EqnCompiler.DepElim
import Lean.Meta.EqnCompiler.CaseValues
import Lean.Meta.EqnCompiler.CaseArraySizes

namespace Lean

@[init] private def regTraceClasses : IO Unit :=
registerTraceClass `Meta.EqnCompiler

end Lean
