/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Match.MatchPatternAttr
import Lean.Meta.Match.Match
import Lean.Meta.Match.CaseValues
import Lean.Meta.Match.CaseArraySizes

namespace Lean

@[init] private def regTraceClasses : IO Unit :=
registerTraceClass `Meta.Match

end Lean
