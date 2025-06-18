/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Attributes


namespace Lean.Compiler

inductive InlineAttributeKind where
  | inline | noinline | macroInline | inlineIfReduce | alwaysInline
  deriving Inhabited, BEq, Hashable

/--
This is an approximate test for testing whether `declName` can be annotated with the `[macro_inline]` attribute or not.
-/
private def isValidMacroInline (declName : Name) : CoreM Bool := do
  let .defnInfo info ← getConstInfo declName
    | return false
  unless info.all.length = 1 do
    -- We do not allow `[macro_inline]` attributes at mutual recursive definitions
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

/--
Changes the inlining behavior. This attribute comes in several variants:
- `@[inline]`: marks the definition to be inlined when it is appropriate.
- `@[inline_if_reduce]`: marks the definition to be inlined if an application of it after inlining
  and applying reduction isn't a `match` expression. This attribute can be used for inlining
  structurally recursive functions.
- `@[noinline]`: marks the definition to never be inlined.
- `@[always_inline]`: marks the definition to always be inlined.
- `@[macro_inline]`: marks the definition to always be inlined at the beginning of compilation.
  This makes it possible to define functions that evaluate some of their parameters lazily.
  Example:
  ```
  @[macro_inline]
  def test (x y : Nat) : Nat :=
    if x = 42 then x else y

  #eval test 42 (2^1000000000000) -- doesn't compute 2^1000000000000
  ```
  Only non-recursive functions may be marked `@[macro_inline]`.
-/
@[builtin_doc]
builtin_initialize inlineAttrs : EnumAttributes InlineAttributeKind ←
  registerEnumAttributes
    [(`inline, "mark definition to be inlined", .inline),
     (`inline_if_reduce, "mark definition to be inlined when resultant term after reduction is not a `cases_on` application", .inlineIfReduce),
     (`noinline, "mark definition to never be inlined", .noinline),
     (`macro_inline, "mark definition to always be inlined before ANF conversion", .macroInline),
     (`always_inline, "mark definition to be always inlined", .alwaysInline)]
    fun declName kind => do
      ofExcept <| checkIsDefinition (← getEnv) declName
      if kind matches .macroInline then
        unless (← isValidMacroInline declName) do
          throwError "invalid use of `[macro_inline]` attribute at `{declName}`, it is not supported in this kind of declaration, declaration must be a non-recursive definition"

def setInlineAttribute (env : Environment) (declName : Name) (kind : InlineAttributeKind) : Except String Environment :=
  inlineAttrs.setValue env declName kind

def getInlineAttribute? (env : Environment) (declName : Name) : Option InlineAttributeKind :=
  inlineAttrs.getValue env declName

private def hasInlineAttrCore (env : Environment) (kind : InlineAttributeKind) (declName : Name) : Bool :=
  match inlineAttrs.getValue env declName with
  | some k => kind == k
  | _ => false

abbrev hasInlineAttribute (env : Environment) (declName : Name) : Bool :=
  hasInlineAttrCore env .inline declName

def hasInlineIfReduceAttribute (env : Environment) (declName : Name) : Bool :=
  hasInlineAttrCore env .inlineIfReduce declName

def hasNoInlineAttribute (env : Environment) (declName : Name) : Bool :=
  hasInlineAttrCore env .noinline declName

def hasMacroInlineAttribute (env : Environment) (declName : Name) : Bool :=
  hasInlineAttrCore env .macroInline declName

abbrev hasAlwaysInlineAttribute (env : Environment) (declName : Name) : Bool :=
  hasInlineAttrCore env .alwaysInline declName

-- TODO: delete rest of the file after we have old code generator

private partial def hasInlineAttrAux (env : Environment) (kind : InlineAttributeKind) (n : Name) : Bool :=
  /- We never inline auxiliary declarations created by eager lambda lifting -/
  if isEagerLambdaLiftingName n then false
  else match inlineAttrs.getValue env n with
    | some k => kind == k
    | none   => if n.isInternal then hasInlineAttrAux env kind n.getPrefix else false

@[export lean_has_inline_attribute]
def hasInlineAttributeOld (env : Environment) (n : Name) : Bool :=
  hasInlineAttrAux env InlineAttributeKind.inline n

@[export lean_has_inline_if_reduce_attribute]
def hasInlineIfReduceAttributeOld (env : Environment) (n : Name) : Bool :=
  hasInlineAttrAux env InlineAttributeKind.inlineIfReduce n

@[export lean_has_noinline_attribute]
def hasNoInlineAttributeOld (env : Environment) (n : Name) : Bool :=
  hasInlineAttrAux env InlineAttributeKind.noinline n

@[export lean_has_macro_inline_attribute]
def hasMacroInlineAttributeOld (env : Environment) (n : Name) : Bool :=
  hasInlineAttrAux env InlineAttributeKind.macroInline n

end Lean.Compiler
