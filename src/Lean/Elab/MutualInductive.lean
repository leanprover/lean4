/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Kyle Miller
-/
prelude
import Lean.Util.ForEachExprWhere
import Lean.Util.ReplaceLevel
import Lean.Util.ReplaceExpr
import Lean.Util.CollectLevelParams
import Lean.Meta.Constructions
import Lean.Meta.CollectFVars
import Lean.Meta.SizeOf
import Lean.Meta.Injective
import Lean.Meta.IndPredBelow
import Lean.Elab.Command
import Lean.Elab.ComputedFields
import Lean.Elab.DefView
import Lean.Elab.DeclUtil
import Lean.Elab.Deriving.Basic
import Lean.Elab.DeclarationRange

/-!
# Elaborator framework for (mutual) inductives

Note(kmill): This file currently is a stub for adding a builtin attribute for https://github.com/leanprover/lean4/pull/6125

-/

namespace Lean.Elab.Command
open Meta

structure InductiveElabDescr where
  deriving Inhabited

/--
Environment extension to register inductive type elaborator commands.
-/
builtin_initialize inductiveElabAttr : KeyedDeclsAttribute InductiveElabDescr ←
  unsafe KeyedDeclsAttribute.init {
    builtinName := `builtin_inductive_elab,
    name := `inductive_elab,
    descr    := "Register an elaborator for inductive types",
    valueTypeName := ``InductiveElabDescr
  }

end Lean.Elab.Command
