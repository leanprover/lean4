/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Elab.Import
public import Lean.Elab.Exception
public import Lean.Elab.Config
public import Lean.Elab.Command
public import Lean.Elab.Term
public import Lean.Elab.App
public import Lean.Elab.Binders
public import Lean.Elab.BinderPredicates
public import Lean.Elab.LetRec
public import Lean.Elab.Frontend
public import Lean.Elab.BuiltinNotation
public import Lean.Elab.Declaration
public import Lean.Elab.Tactic
public import Lean.Elab.Match
-- HACK: must come after `Match` because builtin elaborators (for `match` in this case) do not take priorities
public import Lean.Elab.Quotation
public import Lean.Elab.Syntax
public import Lean.Elab.Do
public import Lean.Elab.StructInst
public import Lean.Elab.StructInstHint
public import Lean.Elab.MutualInductive
public import Lean.Elab.Inductive
public import Lean.Elab.Structure
public import Lean.Elab.Print
public import Lean.Elab.MutualDef
public import Lean.Elab.AuxDef
public import Lean.Elab.PreDefinition
public import Lean.Elab.Deriving
public import Lean.Elab.DeclarationRange
public import Lean.Elab.Extra
public import Lean.Elab.GenInjective
public import Lean.Elab.BuiltinTerm
public import Lean.Elab.Arg
public import Lean.Elab.PatternVar
public import Lean.Elab.ElabRules
public import Lean.Elab.Macro
public import Lean.Elab.Notation
public import Lean.Elab.Mixfix
public import Lean.Elab.MacroRules
public import Lean.Elab.BuiltinCommand
public import Lean.Elab.AssertExists
public import Lean.Elab.Command.WithWeakNamespace
public import Lean.Elab.BuiltinEvalCommand
public import Lean.Elab.RecAppSyntax
public import Lean.Elab.Eval
public import Lean.Elab.Calc
public import Lean.Elab.InheritDoc
public import Lean.Elab.ParseImportsFast
public import Lean.Elab.GuardMsgs
public import Lean.Elab.CheckTactic
public import Lean.Elab.MatchExpr
public import Lean.Elab.Tactic.Doc
public import Lean.Elab.Time
public import Lean.Elab.RecommendedSpelling
public import Lean.Elab.InfoTrees
public import Lean.Elab.ErrorExplanation
public import Lean.Elab.DocString
public import Lean.Elab.DocString.Builtin
public import Lean.Elab.Parallel
