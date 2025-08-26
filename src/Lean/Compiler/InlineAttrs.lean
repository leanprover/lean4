/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Attributes

public section


namespace Lean.Compiler

inductive InlineAttributeKind where
  | inline | noinline | macroInline | inlineIfReduce | alwaysInline
  deriving Inhabited, BEq, Hashable

private def InlineAttributeKind.toAttrString : InlineAttributeKind → String
  | .inline => "inline"
  | .noinline => "noinline"
  | .macroInline => "macro_inline"
  | .inlineIfReduce => "inline_if_reduce"
  | .alwaysInline => "always_inline"

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
      ofExcept <| (checkIsDefinition (← getEnv) declName).mapError fun e =>
        s!"Cannot add attribute `[{kind.toAttrString}]`: {e}"
      if kind matches .macroInline then
        unless (← isValidMacroInline declName) do
          throwError "Cannot add `[macro_inline]` attribute to `{.ofConstName declName}`: This attribute does not support this kind of declaration; only non-recursive definitions are supported"
        withExporting (isExporting := !isPrivateName declName) do
          if !(← getConstInfo declName).isDefinition then
            throwError "invalid `[macro_inline]` attribute, `{.ofConstName declName}` must be an exposed definition"

def setInlineAttribute (env : Environment) (declName : Name) (kind : InlineAttributeKind) : Except String Environment :=
  inlineAttrs.setValue env declName kind

def getInlineAttribute? (env : Environment) (declName : Name) : Option InlineAttributeKind :=
  inlineAttrs.getValue env declName

private def hasInlineAttrCore (env : Environment) (kind : InlineAttributeKind) (declName : Name) : Bool :=
  match inlineAttrs.getValue env declName with
  | some k => kind == k
  | _ => false

@[inline] def hasInlineAttribute (env : Environment) (declName : Name) : Bool :=
  hasInlineAttrCore env .inline declName

def hasInlineIfReduceAttribute (env : Environment) (declName : Name) : Bool :=
  hasInlineAttrCore env .inlineIfReduce declName

def hasNoInlineAttribute (env : Environment) (declName : Name) : Bool :=
  hasInlineAttrCore env .noinline declName

def hasMacroInlineAttribute (env : Environment) (declName : Name) : Bool :=
  hasInlineAttrCore env .macroInline declName

@[inline] def hasAlwaysInlineAttribute (env : Environment) (declName : Name) : Bool :=
  hasInlineAttrCore env .alwaysInline declName

end Lean.Compiler
