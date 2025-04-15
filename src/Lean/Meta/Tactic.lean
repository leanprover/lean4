/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Intro
import Lean.Meta.Tactic.Assumption
import Lean.Meta.Tactic.Contradiction
import Lean.Meta.Tactic.Apply
import Lean.Meta.Tactic.Revert
import Lean.Meta.Tactic.Clear
import Lean.Meta.Tactic.Assert
import Lean.Meta.Tactic.Rewrite
import Lean.Meta.Tactic.Generalize
import Lean.Meta.Tactic.Replace
import Lean.Meta.Tactic.Induction
import Lean.Meta.Tactic.Cases
import Lean.Meta.Tactic.ElimInfo
import Lean.Meta.Tactic.Delta
import Lean.Meta.Tactic.Constructor
import Lean.Meta.Tactic.Simp
import Lean.Meta.Tactic.AuxLemma
import Lean.Meta.Tactic.SplitIf
import Lean.Meta.Tactic.Split
import Lean.Meta.Tactic.TryThis
import Lean.Meta.Tactic.Cleanup
import Lean.Meta.Tactic.Unfold
import Lean.Meta.Tactic.Rename
import Lean.Meta.Tactic.AC
import Lean.Meta.Tactic.Refl
import Lean.Meta.Tactic.Congr
import Lean.Meta.Tactic.Repeat
import Lean.Meta.Tactic.NormCast
import Lean.Meta.Tactic.IndependentOf
import Lean.Meta.Tactic.Symm
import Lean.Meta.Tactic.Backtrack
import Lean.Meta.Tactic.SolveByElim
import Lean.Meta.Tactic.FunInd
import Lean.Meta.Tactic.Rfl
import Lean.Meta.Tactic.Rewrites
import Lean.Meta.Tactic.Grind
import Lean.Meta.Tactic.Ext
import Lean.Meta.Tactic.Try
