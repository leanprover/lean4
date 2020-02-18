/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Util.CollectFVars
import Init.Lean.Util.CollectLevelParams
import Init.Lean.Util.CollectMVars
import Init.Lean.Util.FindMVar
import Init.Lean.Util.MonadCache
import Init.Lean.Util.PPExt
import Init.Lean.Util.PPGoal
import Init.Lean.Util.Path
import Init.Lean.Util.Profile
import Init.Lean.Util.RecDepth
import Init.Lean.Util.Sorry
import Init.Lean.Util.Trace
import Init.Lean.Util.WHNF
import Init.Lean.Util.FindExpr
import Init.Lean.Util.ReplaceExpr
