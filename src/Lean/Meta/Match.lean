/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Match.MatchPatternAttr
public import Lean.Meta.Match.Match
public import Lean.Meta.Match.CaseValues
public import Lean.Meta.Match.CaseArraySizes
public import Lean.Meta.Match.MatchEqs

public section

namespace Lean

builtin_initialize registerTraceClass `Meta.Match

end Lean
