/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Parser.Basic
import Lean.Attributes
import Lean.MonadEnv
namespace Lean.Elab

structure Attribute where
  kind     : AttributeKind := AttributeKind.global
  name     : Name
  args     : Syntax := Syntax.missing

instance : ToFormat Attribute where
  format attr :=
   let kindStr := match attr.kind with
     | AttributeKind.global => ""
     | AttributeKind.local  => "local "
     | AttributeKind.scoped => "scoped "
   Format.bracket "@[" f!"{kindStr}{attr.name}{if attr.args.isMissing then "" else toString attr.args}" "]"

instance : Inhabited Attribute where
  default := { name := arbitrary }

/-
  ```
  attrKind := parser! optional («scoped» <|> «local»)
  ```
-/
def toAttributeKind [Monad m] [MonadResolveName m] [MonadError m] (attrKindStx : Syntax) : m AttributeKind := do
  if attrKindStx[0].isNone then
    return AttributeKind.global
  else if attrKindStx[0][0].getKind == `Lean.Parser.Term.scoped then
    if (← getCurrNamespace).isAnonymous then
      throwError! "scoped attributes must be used inside namespaces"
    return AttributeKind.scoped
  else
    return AttributeKind.local

def mkAttrKindGlobal : Syntax :=
  Syntax.node `Lean.Parser.Term.attrKind #[mkNullNode]

def elabAttr {m} [Monad m] [MonadEnv m] [MonadResolveName m] [MonadError m] (stx : Syntax) : m Attribute := do
  -- attrKind >> rawIdent >> many attrArg
  let attrKind ← toAttributeKind stx[0]
  let nameStx := stx[1]
  let attrName ← match nameStx.isIdOrAtom? with
    | none     => withRef nameStx $ throwError "identifier expected"
    | some str => pure $ Name.mkSimple str
  unless isAttribute (← getEnv) attrName do
    throwError! "unknown attribute [{attrName}]"
  let args := stx[2]
  pure { kind := attrKind, name := attrName, args := args }

-- sepBy1 attrInstance ", "
def elabAttrs {m} [Monad m] [MonadEnv m] [MonadResolveName m] [MonadError m] (stx : Syntax)
    : m (Array Attribute) := do
  let mut attrs := #[]
  for attr in stx.getSepArgs do
    attrs := attrs.push (← elabAttr attr)
  return attrs

-- parser! "@[" >> sepBy1 attrInstance ", " >> "]"
def elabDeclAttrs {m} [Monad m] [MonadEnv m] [MonadResolveName m] [MonadError m] (stx : Syntax) : m (Array Attribute) :=
  elabAttrs stx[1]

end Lean.Elab
