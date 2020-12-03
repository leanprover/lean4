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
  scoped : Bool := false
  name   : Name
  args   : Syntax := Syntax.missing

instance : ToFormat Attribute where
  format attr :=
    Format.bracket "@[" f!"{if attr.scoped then "scoped" else ""}{attr.name}{if attr.args.isMissing then "" else toString attr.args}" "]"

instance : Inhabited Attribute where
  default := { name := arbitrary }

def elabAttr {m} [Monad m] [MonadEnv m] [MonadExceptOf Exception m] [MonadRef m] [AddErrorMessageContext m] (stx : Syntax) : m Attribute := do
  -- optional "scoped" >> rawIdent >> many attrArg
  let scoped  := false -- !stx[0].isNone
  let nameStx := stx[0] -- TODO: change to 1
  let attrName ← match nameStx.isIdOrAtom? with
    | none     => withRef nameStx $ throwError "identifier expected"
    | some str => pure $ Name.mkSimple str
  unless isAttribute (← getEnv) attrName do
    throwError! "unknown attribute [{attrName}]"
  let mut args := stx[1] -- TODO: change to 2
  -- the old frontend passes Syntax.missing for empty args, for reasons
  if args.getNumArgs == 0 then
    args := Syntax.missing
  pure { scoped := scoped, name := attrName, args := args }

-- sepBy1 attrInstance ", "
def elabAttrs {m} [Monad m] [MonadEnv m] [MonadExceptOf Exception m] [MonadRef m] [AddErrorMessageContext m] (stx : Syntax) : m (Array Attribute) := do
  let mut attrs := #[]
  for attr in stx.getSepArgs do
    attrs := attrs.push (← elabAttr attr)
  return attrs

-- parser! "@[" >> sepBy1 attrInstance ", " >> "]"
def elabDeclAttrs {m} [Monad m] [MonadEnv m] [MonadExceptOf Exception m] [MonadRef m] [AddErrorMessageContext m] (stx : Syntax) : m (Array Attribute) :=
  elabAttrs stx[1]

end Lean.Elab
