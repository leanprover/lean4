/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Attributes
import Lean.Compiler.Util

namespace Lean.Compiler

inductive InlineAttributeKind where
  | inline | noinline | macroInline | inlineIfReduce
  deriving Inhabited, BEq

/--
  This is an approximate test for testing whether `declName` can be annotated with the `[macroInline]` attribute or not.
-/
private def isValidMacroInline (declName : Name) : CoreM Bool := do
  let .defnInfo info ← getConstInfo declName
    | return false
  unless info.all.length = 1 do
    -- We do not allow `[macroInline]` attributes at mutual recursive definitions
    return false
  let env ← getEnv
  let isRec (declName' : Name) : Bool :=
    isBRecOnRecursor env declName' ||
    declName' == ``WellFounded.fix ||
    declName' == declName ++ `_unary -- Auxiliary declaration created by `WF` module
  if Option.isSome <| info.value.find? fun e => e.isConst && isRec e.constName! then
    -- It contains a `brecOn` or `WellFounded.fix` application. So, it should be recursvie
    return false
  return true

builtin_initialize inlineAttrs : EnumAttributes InlineAttributeKind ←
  registerEnumAttributes `inlineAttrs
    [(`inline, "mark definition to always be inlined", InlineAttributeKind.inline),
     (`inlineIfReduce, "mark definition to be inlined when resultant term after reduction is not a `cases_on` application", InlineAttributeKind.inlineIfReduce),
     (`noinline, "mark definition to never be inlined", InlineAttributeKind.noinline),
     (`macroInline, "mark definition to always be inlined before ANF conversion", InlineAttributeKind.macroInline)]
    fun declName kind => do
      ofExcept <| checkIsDefinition (← getEnv) declName
      if kind matches .macroInline then
        unless (← isValidMacroInline declName) do
          throwError "invalid use of `[macro_inline]` attribute at `{declName}`, it is not supported in this kind of declaration, declaration must be a non-recursive definition"

private partial def hasInlineAttrAux (env : Environment) (kind : InlineAttributeKind) (n : Name) : Bool :=
  /- We never inline auxiliary declarations created by eager lambda lifting -/
  if isEagerLambdaLiftingName n then false
  else match inlineAttrs.getValue env n with
    | some k => kind == k
    | none   => if n.isInternal then hasInlineAttrAux env kind n.getPrefix else false

@[export lean_has_inline_attribute]
def hasInlineAttribute (env : Environment) (n : Name) : Bool :=
  hasInlineAttrAux env InlineAttributeKind.inline n

@[export lean_has_inline_if_reduce_attribute]
def hasInlineIfReduceAttribute (env : Environment) (n : Name) : Bool :=
  hasInlineAttrAux env InlineAttributeKind.inlineIfReduce n

@[export lean_has_noinline_attribute]
def hasNoInlineAttribute (env : Environment) (n : Name) : Bool :=
  hasInlineAttrAux env InlineAttributeKind.noinline n

@[export lean_has_macro_inline_attribute]
def hasMacroInlineAttribute (env : Environment) (n : Name) : Bool :=
  hasInlineAttrAux env InlineAttributeKind.macroInline n

def setInlineAttribute (env : Environment) (declName : Name) (kind : InlineAttributeKind) : Except String Environment :=
  inlineAttrs.setValue env declName kind

end Lean.Compiler
