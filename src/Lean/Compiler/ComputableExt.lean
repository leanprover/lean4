/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.EnvExtension
public import Lean.Meta.Basic
import Lean.ProjFns
import Lean.AuxRecursor
import Lean.Compiler.CSimpAttr
import Lean.Compiler.InlineAttrs
import Lean.Meta.InferType
import Lean.Meta.Match.MatcherInfo

public section

namespace Lean

-- `sync` as it's written to from both main branch and codegen branch
builtin_initialize computableExt : TagDeclarationExtension ← mkTagDeclarationExtension (asyncMode := .sync)

@[deprecated "This function no longer has an effect" (since := "2026-08-04")]
def addNoncomputable (env : Environment) (_declName : Name) : Environment := env

/-- This function is only meant to be used within the compiler. -/
def addComputable (env : Environment) (declName : Name) : Environment :=
  computableExt.addEntry env declName

-- keep in sync with `visitApp` in `Lean.Compiler.LCNF.ToLCNF`
private def hardcodedSpecialCases : Array Name :=
  #[``Quot.lift, ``Quot.mk, ``Eq.rec, ``Eq.recOn, ``Eq.ndrec, ``HEq.rec, ``HEq.ndrec,
    ``And.rec, ``Iff.rec, ``False.rec, ``Empty.rec, ``lcUnreachable]

/--
Returns `true` when the given declaration is directly computable, that is, if this function has
compiled code or has an `@[extern]` or `@[implemented_by]` attribute.
-/
def isDirectlyComputable (env : Environment) (declName : Name)
    (asyncMode := computableExt.toEnvExtension.asyncMode) : Bool :=
  computableExt.isTagged (asyncMode := asyncMode) env declName

/--
Returns `true` when the given declaration is computable, that is, if this function has compiled
code or has special support from the compiler.

Note: Proofs and type formers are usually not considered as computable using the function.
-/
def isComputable (env : Environment) (declName : Name)
    (asyncMode := computableExt.toEnvExtension.asyncMode) : Bool :=
  isDirectlyComputable env declName asyncMode ||
    env.isProjectionFn declName || env.isConstructor declName ||
    isCasesOnLike env declName || isNoConfusion env declName ||
    (Compiler.CSimp.ext.getState env).map.contains declName ||
    -- TODO: enforce that `macro_inline`d declarations are *actually* computable
    Compiler.hasMacroInlineAttribute env declName ||
    -- "morally" `macro_inline`
    Meta.isMatcherCore env declName ||
    Meta.isMatcherLikeCore env declName ||
    hardcodedSpecialCases.contains declName

/--
Returns `true` when the given declaration is computable or irrelevant, that is, if this function
has compiled code, special support from the compiler or is a proof or type former.
-/
def isComputableOrIrrelevant (declName : Name)
    (asyncMode := computableExt.toEnvExtension.asyncMode) : MetaM Bool := do
  if isComputable (← getEnv) declName asyncMode then
    return true
  let val ← getConstVal declName
  Meta.isProp val.type <||> Meta.isTypeFormerType val.type

@[deprecated "Use `!(← isComputableOrIrrelevant env declName)`" (since := "2026-08-04")]
abbrev isNoncomputable (env : Environment) (declName : Name)
    (asyncMode := computableExt.toEnvExtension.asyncMode) : Bool :=
  !isComputable env declName asyncMode

end Lean
