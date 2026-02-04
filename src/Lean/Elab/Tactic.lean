/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
module

prelude
public import Lean.Elab.Tactic.Basic
public import Lean.Elab.Tactic.ElabTerm
public import Lean.Elab.Tactic.Induction
public import Lean.Elab.Tactic.Generalize
public import Lean.Elab.Tactic.Injection
public import Lean.Elab.Tactic.Match
public import Lean.Elab.Tactic.Rewrite
public import Lean.Elab.Tactic.Location
public import Lean.Elab.Tactic.SimpTrace
public import Lean.Elab.Tactic.Simp
public import Lean.Elab.Tactic.Simproc
public import Lean.Elab.Tactic.BuiltinTactic
public import Lean.Elab.Tactic.Split
public import Lean.Elab.Tactic.Conv
public import Lean.Elab.Tactic.Delta
public import Lean.Elab.Tactic.Meta
public import Lean.Elab.Tactic.Unfold
public import Lean.Elab.Tactic.Calc
public import Lean.Elab.Tactic.Congr
public import Lean.Elab.Tactic.Guard
public import Lean.Elab.Tactic.RCases
public import Lean.Elab.Tactic.Repeat
public import Lean.Elab.Tactic.Ext
public import Lean.Elab.Tactic.Change
public import Lean.Elab.Tactic.FalseOrByContra
public import Lean.Elab.Tactic.Omega
public import Lean.Elab.Tactic.Simpa
public import Lean.Elab.Tactic.NormCast
public import Lean.Elab.Tactic.Symm
public import Lean.Elab.Tactic.SolveByElim
public import Lean.Elab.Tactic.LibrarySearch
public import Lean.Elab.Tactic.ShowTerm
public import Lean.Elab.Tactic.Rfl
public import Lean.Elab.Tactic.Rewrites
public import Lean.Elab.Tactic.DiscrTreeKey
public import Lean.Elab.Tactic.BVDecide
public import Lean.Elab.Tactic.BoolToPropSimps
public import Lean.Elab.Tactic.Classical
public import Lean.Elab.Tactic.Grind
public import Lean.Elab.Tactic.Monotonicity
public import Lean.Elab.Tactic.Try
public import Lean.Elab.Tactic.AsAuxLemma
public import Lean.Elab.Tactic.TreeTacAttr
public import Lean.Elab.Tactic.ExposeNames
public import Lean.Elab.Tactic.SimpArith
public import Lean.Elab.Tactic.Show
public import Lean.Elab.Tactic.Lets
public import Lean.Elab.Tactic.Do
public import Lean.Elab.Tactic.Decide
