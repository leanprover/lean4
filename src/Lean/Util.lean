/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Util.CollectFVars
import Lean.Util.CollectLevelParams
import Lean.Util.CollectMVars
import Lean.Util.CollectLevelMVars
import Lean.Util.FindMVar
import Lean.Util.FindLevelMVar
import Lean.Util.MonadCache
import Lean.Util.PPExt
import Lean.Util.Path
import Lean.Util.Profile
import Lean.Util.RecDepth
import Lean.Util.ShareCommon
import Lean.Util.Sorry
import Lean.Util.Trace
import Lean.Util.FindExpr
import Lean.Util.ReplaceExpr
import Lean.Util.ForEachExpr
import Lean.Util.ForEachExprWhere
import Lean.Util.ReplaceLevel
import Lean.Util.FoldConsts
import Lean.Util.SCC
import Lean.Util.TestExtern
import Lean.Util.OccursCheck
import Lean.Util.HasConstCache
import Lean.Util.FileSetupInfo
import Lean.Util.Heartbeats
import Lean.Util.SearchPath
import Lean.Util.SafeExponentiation
import Lean.Util.NumObjs
import Lean.Util.NumApps
import Lean.Util.FVarSubset
import Lean.Util.SortExprs
