/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Elab.Import
import Lean.Elab.Exception
import Lean.Elab.StrategyAttrs
import Lean.Elab.Command
import Lean.Elab.Term
import Lean.Elab.App
import Lean.Elab.Binders
import Lean.Elab.Quotation
import Lean.Elab.Frontend
import Lean.Elab.BuiltinNotation
import Lean.Elab.Declaration
import Lean.Elab.Tactic
import Lean.Elab.Syntax
import Lean.Elab.Match
import Lean.Elab.DoNotation
import Lean.Elab.StructInst
