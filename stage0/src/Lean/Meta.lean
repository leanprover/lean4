/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Basic
import Lean.Meta.LevelDefEq
import Lean.Meta.WHNF
import Lean.Meta.InferType
import Lean.Meta.FunInfo
import Lean.Meta.ExprDefEq
import Lean.Meta.DiscrTree
import Lean.Meta.Reduce
import Lean.Meta.Instances
import Lean.Meta.AbstractMVars
import Lean.Meta.SynthInstance
import Lean.Meta.AppBuilder
import Lean.Meta.Tactic
import Lean.Meta.KAbstract
import Lean.Meta.RecursorInfo
import Lean.Meta.GeneralizeTelescope
import Lean.Meta.Match
import Lean.Meta.ReduceEval
import Lean.Meta.Closure
import Lean.Meta.AbstractNestedProofs
import Lean.Meta.ForEachExpr
import Lean.Meta.Transform
import Lean.Meta.PPGoal
import Lean.Meta.UnificationHint
import Lean.Meta.Inductive
import Lean.Meta.SizeOf
import Lean.Meta.IndPredBelow
import Lean.Meta.Coe
import Lean.Meta.SortLocalDecls
import Lean.Meta.CollectFVars
import Lean.Meta.GeneralizeVars
import Lean.Meta.Injective
import Lean.Meta.Structure
import Lean.Meta.Constructions
import Lean.Meta.CongrTheorems
import Lean.Meta.Eqns
