/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Parser.Basic
import Lean.Attributes
import Lean.MonadEnv
namespace Lean.Elab

structure Attribute :=
(name : Name) (args : Syntax := Syntax.missing)

instance : ToFormat Attribute := ⟨fun attr =>
  Format.bracket "@[" (toString attr.name ++ (if attr.args.isMissing then "" else toString attr.args)) "]"⟩

instance : Inhabited Attribute := ⟨{ name := arbitrary _ }⟩

def elabAttr {m} [Monad m] [MonadEnv m] [MonadExceptOf Exception m] [Ref m] [AddErrorMessageContext m] (stx : Syntax) : m Attribute := do
  -- rawIdent >> many attrArg
  let nameStx := stx[0]
  let attrName ← match nameStx.isIdOrAtom? with
    | none     => withRef nameStx $ throwError "identifier expected"
    | some str => pure $ Name.mkSimple str
  unless isAttribute (← getEnv) attrName do
    throwError! "unknown attribute [{attrName}]"
  let mut args := stx[1]
  -- the old frontend passes Syntax.missing for empty args, for reasons
  if args.getNumArgs == 0 then
    args := Syntax.missing
  pure { name := attrName, args := args }

-- sepBy1 attrInstance ", "
def elabAttrs {m} [Monad m] [MonadEnv m] [MonadExceptOf Exception m] [Ref m] [AddErrorMessageContext m] (stx : Syntax) : m (Array Attribute) := do
  let mut attrs := #[]
  for attr in stx.getSepArgs do
    attrs := attrs.push (← elabAttr attr)
  return attrs

-- parser! "@[" >> sepBy1 attrInstance ", " >> "]"
def elabDeclAttrs {m} [Monad m] [MonadEnv m] [MonadExceptOf Exception m] [Ref m] [AddErrorMessageContext m] (stx : Syntax) : m (Array Attribute) :=
  elabAttrs stx[1]

end Lean.Elab
