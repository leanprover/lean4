/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Elab.Import
import Lean.Elab.Exception
import Lean.Elab.Config
import Lean.Elab.Command
import Lean.Elab.Term
import Lean.Elab.App
import Lean.Elab.Binders
import Lean.Elab.BinderPredicates
import Lean.Elab.LetRec
import Lean.Elab.Frontend
import Lean.Elab.BuiltinNotation
import Lean.Elab.Declaration
import Lean.Elab.Tactic
import Lean.Elab.Match
-- HACK: must come after `Match` because builtin elaborators (for `match` in this case) do not take priorities
import Lean.Elab.Quotation
import Lean.Elab.Syntax
import Lean.Elab.Do
import Lean.Elab.StructInst
import Lean.Elab.MutualInductive
import Lean.Elab.Inductive
import Lean.Elab.Structure
import Lean.Elab.Print
import Lean.Elab.MutualDef
import Lean.Elab.AuxDef
import Lean.Elab.PreDefinition
import Lean.Elab.Deriving
import Lean.Elab.DeclarationRange
import Lean.Elab.Extra
import Lean.Elab.GenInjective
import Lean.Elab.BuiltinTerm
import Lean.Elab.Arg
import Lean.Elab.PatternVar
import Lean.Elab.ElabRules
import Lean.Elab.Macro
import Lean.Elab.Notation
import Lean.Elab.Mixfix
import Lean.Elab.MacroRules
import Lean.Elab.BuiltinCommand
import Lean.Elab.BuiltinEvalCommand
import Lean.Elab.RecAppSyntax
import Lean.Elab.Eval
import Lean.Elab.Calc
import Lean.Elab.InheritDoc
import Lean.Elab.ParseImportsFast
import Lean.Elab.GuardMsgs
import Lean.Elab.CheckTactic
import Lean.Elab.MatchExpr
import Lean.Elab.Tactic.Doc
import Lean.Elab.Time
