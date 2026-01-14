/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
module

prelude
public import Lean.Elab.Util
public import Lean.Compiler.InitAttr
import Lean.Parser.Term

public section
namespace Lean.Elab

structure Attribute where
  kind  : AttributeKind := AttributeKind.global
  name  : Name
  stx   : Syntax := Syntax.missing
  deriving Inhabited

instance : ToFormat Attribute where
  format attr :=
   let kindStr := match attr.kind with
     | AttributeKind.global => ""
     | AttributeKind.local  => "local "
     | AttributeKind.scoped => "scoped "
   Format.bracket "@[" f!"{kindStr}{attr.name}{toString attr.stx}" "]"

/--
  ```
  attrKind := leading_parser optional («scoped» <|> «local»)
  ```
-/
def toAttributeKind (attrKindStx : Syntax) : MacroM AttributeKind := do
  if attrKindStx[0].isNone then
    return AttributeKind.global
  else if attrKindStx[0][0].getKind == ``Lean.Parser.Term.scoped then
    if (← Macro.getCurrNamespace).isAnonymous then
      throw <| Macro.Exception.error (← getRef) "Scoped attributes must be used inside namespaces"
    return AttributeKind.scoped
  else
    return AttributeKind.local

def mkAttrKindGlobal : Syntax :=
  mkNode ``Lean.Parser.Term.attrKind #[mkNullNode]

def elabAttr [Monad m] [MonadEnv m] [MonadResolveName m] [MonadError m] [MonadMacroAdapter m] [MonadRecDepth m] [MonadTrace m] [MonadOptions m] [AddMessageContext m] [MonadLiftT IO m] [MonadFinally m] (attrInstance : Syntax) : m Attribute := do
  -- Resolving the attribute itself can be done in the private scope; running the attribute handler
  -- will later be done in a scope determined by `applyAttributesCore`.
  withoutExporting do
    /- attrInstance     := ppGroup $ leading_parser attrKind >> attrParser -/
    let attrKind ← liftMacroM <| toAttributeKind attrInstance[0]
    let attr := attrInstance[1]
    let attr ← liftMacroM <| expandMacros attr
    let attrName ← if attr.getKind == ``Parser.Attr.simple then
      pure attr[0].getId.eraseMacroScopes
    else match attr.getKind with
      | .str _ s => pure <| Name.mkSimple s
      | _ => throwErrorAt attr  "Unknown attribute"
    let .ok _impl := getAttributeImpl (← getEnv) attrName
      | throwError "Unknown attribute `[{attrName}]`"
    if let .ok impl := getAttributeImpl (← getEnv) attrName then
      if regularInitAttr.getParam? (← getEnv) impl.ref |>.isSome then  -- skip `builtin_initialize` attributes
        recordExtraModUseFromDecl (isMeta := true) impl.ref
    /- The `AttrM` does not have sufficient information for expanding macros in `args`.
      So, we expand them before here before we invoke the attributer handlers implemented using `AttrM`. -/
    return { kind := attrKind, name := attrName, stx := attr }

def elabAttrs [Monad m] [MonadEnv m] [MonadResolveName m] [MonadError m] [MonadMacroAdapter m] [MonadRecDepth m] [MonadTrace m] [MonadOptions m] [AddMessageContext m] [MonadLog m] [MonadLiftT IO m] [MonadFinally m] (attrInstances : Array Syntax) : m (Array Attribute) := do
  let mut attrs := #[]
  for attr in attrInstances do
    try
      attrs := attrs.push (← withRef attr do elabAttr attr)
    catch ex =>
      logException ex
  return attrs

-- leading_parser "@[" >> sepBy1 attrInstance ", " >> "]"
def elabDeclAttrs [Monad m] [MonadEnv m] [MonadResolveName m] [MonadError m] [MonadMacroAdapter m] [MonadRecDepth m] [MonadTrace m] [MonadOptions m] [AddMessageContext m] [MonadLog m] [MonadLiftT IO m] [MonadFinally m] (stx : Syntax) : m (Array Attribute) :=
  elabAttrs stx[1].getSepArgs

end Lean.Elab
