/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Meta.Basic
import Init.Lean.Meta.LevelDefEq
import Init.Lean.Meta.WHNF
import Init.Lean.Meta.InferType
import Init.Lean.Meta.FunInfo
import Init.Lean.Meta.ExprDefEq
import Init.Lean.Meta.DiscrTree
import Init.Lean.Meta.Reduce
import Init.Lean.Meta.Instances
import Init.Lean.Meta.AbstractMVars
import Init.Lean.Meta.SynthInstance
import Init.Lean.Meta.AppBuilder
import Init.Lean.Meta.Tactic
import Init.Lean.Meta.Message
import Init.Lean.Meta.KAbstract

namespace Lean
export Meta (MetaM)
end Lean
